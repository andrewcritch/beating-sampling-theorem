import BstLean.Part276Latitude
import BstLean.Part276NodeTrace

/-! The sharp stored-table event at dimension 12224 with the paper's four
allowances. The event is guarded by the World window `θ ≤ 0.54`. -/
namespace BstLean.Part276
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223 BstLean.Part242

/-- The four allowances of the stored row `chain48q16`, rows 12000 to 13224. -/
noncomputable def fourA : Fin 4 → ℝ :=
  ![335006690 / 10 ^ 10, 163940354 / 10 ^ 10, 1392172484 / 10 ^ 10, 122205006 / 10 ^ 10]

theorem fourA_pos (i : Fin 4) : 0 < fourA i := by
  fin_cases i <;> norm_num [fourA]

/-- The location and energy table thresholds are the sums of the allowances. -/
noncomputable def tableF : ℝ := 498947044 / 10 ^ 10
noncomputable def tableW : ℝ := 1514377490 / 10 ^ 10

theorem tableF_eq : fourA 0 + fourA 1 = tableF := by norm_num [fourA, tableF]
theorem tableW_eq : fourA 2 + fourA 3 = tableW := by norm_num [fourA, tableW]

def tightW {n : ℕ} (wr : WRet n) : Prop :=
  windowW wr ∧ BstLean.Part150.thetaC wr.2 (tau0p wr.1) ≤ 54 / 100

theorem measurableSet_tightW {n : ℕ} : MeasurableSet {wr : WRet n | tightW wr} := by
  have ht : Measurable (fun wr : WRet n => tau0p wr.1) := measurable_tau0p.comp measurable_fst
  have hθ : Measurable (fun wr : WRet n => BstLean.Part150.thetaC wr.2 (tau0p wr.1)) := by
    unfold BstLean.Part150.thetaC
    exact ((ht.pow_const 2).const_mul _).div
      (((BstLean.Part150.measurable_rhoC (n := n)).comp (measurable_snd.prodMk ht)).pow_const 2)
  exact measurableSet_windowW.inter (measurableSet_le hθ measurable_const)

/-- The World window of the replacement theorem gives the tight table guard. -/
theorem tightW_of_window {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hW : WINDOW (paperDesignP n) c) :
    tightW c.1 := by
  have h := window_theta hn c hW
  have h1 : 46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (tau0p c.1.1) := h.1
  have h2 : BstLean.Part150.thetaC c.1.2 (tau0p c.1.1) ≤ 54 / 100 := h.2
  exact ⟨⟨hW.2.1, h1, by linarith⟩, h2⟩

/-- The tight guard gives the World window on every retained value with the same World part. -/
theorem window_of_tightW {n : ℕ} (hn : 1 ≤ n) {wr : WRet n} (hw : tightW wr) (θ : AHid n) :
    WINDOW (paperDesignP n) (mkR wr θ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : wr.2 ≠ 0 := BstLean.Part172.sg_wr_ne hn hw.1
  have hτ : 0 < tau0p wr.1 := hw.1.1
  have hden : 0 < normSq wr.2 + (n : ℝ) * tau0p wr.1 ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hτ))
  have h1 := hw.1.2.1
  have h2 := hw.2
  unfold BstLean.Part150.thetaC BstLean.Part150.rhoC at h1 h2
  rw [sq_sqrt hden.le] at h1 h2
  refine ⟨hc, hτ, ?_, ?_⟩
  · exact (le_div_iff₀ hden).mp h1
  · exact (div_le_iff₀ hden).mp h2

def sharpTable : Set (Ret 12224) := {c | tightW c.1 →
  intF c ≤ tableF ^ 8 ∧ intW c ≤ tableW ^ 8}

theorem sharpTable_measurable : MeasurableSet sharpTable := by
  have hw : MeasurableSet {c : Ret 12224 | tightW c.1} :=
    measurableSet_tightW.preimage measurable_fst
  have hf := measurableSet_le (measurable_intF_comp (n := 12224) measurable_id)
    (measurable_const (a := tableF ^ 8))
  have he := measurableSet_le (measurable_intW_comp (n := 12224) measurable_id)
    (measurable_const (a := tableW ^ 8))
  have heq : sharpTable = {c : Ret 12224 | tightW c.1}ᶜ ∪
      ({c : Ret 12224 | intF c ≤ tableF ^ 8} ∩ {c : Ret 12224 | intW c ≤ tableW ^ 8}) := by
    ext c
    simp only [sharpTable, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : tightW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

noncomputable def fourError (c : Ret 12224) (i : Fin 4) (a : Ix 12224) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem fourError_decomposition (c : Ret 12224) (a : Ix 12224) :
    fourError c 0 a + fourError c 1 a = exF c a ∧
    fourError c 2 a + fourError c 3 a = exW c a :=
  originalFour_decomposition c (gW c.1 a) (A2 c)

theorem sharpTable_of_moments {c : Ret 12224}
    (h : ∀ i, MomentBound (muI 12224) (biasOrder i) (fourError c i) (fourA i)) :
    c ∈ sharpTable := by
  have hb (i : Fin 4) : MomentBound (muI 12224) 8 (fourError c i) (fourA i) :=
    (h i).lower (by norm_num) (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => fourError c 0 a + fourError c 1 a) = exF c :=
    funext fun a => (fourError_decomposition c a).1
  have heW : (fun a => fourError c 2 a + fourError c 3 a) = exW c :=
    funext fun a => (fourError_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by rw [tableF_eq])
  · exact hWi.2.trans (by rw [tableW_eq])

noncomputable def nodeIndex (wr : WRet 12224) (a : Ix 12224) : Fin (Js 12224) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem nodeIndex_measurable (wr : WRet 12224) : Measurable (nodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [nodeIndex, gW, Fin.ext_iff]

noncomputable def nodeMeasure (wr : WRet 12224) : Measure (Fin (Js 12224)) :=
  (muI 12224).map (nodeIndex wr)

theorem nodeMeasure_mass (wr : WRet 12224) : nodeMeasure wr univ = 1 := by
  rw [nodeMeasure, Measure.map_apply (nodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem sharpTable_of_second_layer_good (c : Ret 12224)
    (M : Matrix (Fin (mA 12224)) (Fin (mA 12224)) ℝ)
    (h : M ∉ ⋃ i, momentBad (nodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourA i)) :
    withA2 c M ∈ sharpTable := by
  apply sharpTable_of_moments
  intro i
  have hi : M ∉ momentBad (nodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourA i) :=
    fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
  refine ⟨?_, (fourA_pos i).le, ?_⟩
  · have hf : fourError (withA2 c M) i = (fun g : Fin (Js 12224) =>
        originalFourErrors c i g.val M) ∘ nodeIndex c.1 := rfl
    rw [hf]
    exact (measurable_of_finite _).comp (nodeIndex_measurable c.1)
  · change (∫⁻ a, ENNReal.ofReal (|originalFourErrors c i (gW c.1 a) M| ^ biasOrder i)
      ∂muI 12224) ≤ _
    have he : (∫⁻ a, ENNReal.ofReal (|originalFourErrors c i (gW c.1 a) M| ^ biasOrder i)
        ∂muI 12224) = ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
          ∂nodeMeasure c.1 := by
      rw [nodeMeasure, lintegral_map (measurable_of_finite _) (nodeIndex_measurable c.1)]
      rfl
    rw [he]
    exact le_of_not_gt hi

theorem sharpTable_bad_subset (c : Ret 12224) :
    {M | withA2 c M ∉ sharpTable} ⊆
      ⋃ i, momentBad (nodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourA i) := by
  intro M hM
  by_contra hg
  exact hM (sharpTable_of_second_layer_good c M hg)

/-- The node order-twelve moment of the actual node measure under the tight guard. -/
theorem nodeMeasure_moment12 {wr : WRet 12224} (hw : tightW wr) :
    ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12) ∂nodeMeasure wr ≤
      ENNReal.ofReal ((5435 / 10000 : ℝ) ^ 12) := by
  have hW := window_of_tightW (by norm_num) hw (0 : AHid 12224)
  rw [nodeMeasure, lintegral_map (measurable_of_finite _) (nodeIndex_measurable wr)]
  have hδ : (0 : ℝ) < 1 / 10000 := by norm_num
  have h := node_latitude_moment12 (by norm_num) (mkR wr 0) hW hδ
  refine (le_of_eq_of_le ?_ h).trans (ENNReal.ofReal_le_ofReal ?_)
  · rfl
  have ht := bulkTailMass_small (by norm_num) (mkR wr 0) hW
  have hθ := window_theta (by norm_num) (mkR wr 0) hW
  have hθ0 : (0 : ℝ) ≤ BstLean.Part150.thetaC (mkR wr 0).1.2 ((paperDesignP 12224).tau0 (mkR wr 0)) := by
    have := hθ.1; change (0 : ℝ) ≤ BstLean.Part150.thetaC (mkR wr 0).1.2 (tauR (mkR wr 0)); linarith
  have hθ1 : BstLean.Part150.thetaC (mkR wr 0).1.2 ((paperDesignP 12224).tau0 (mkR wr 0)) ≤ 54 / 100 :=
    hθ.2
  have hmono := BstLean.Part212.latitudeCoefficient_mono (n := 12224) (p := 12) (by norm_num)
    (by norm_num) hθ0 hθ1 (by norm_num)
  have hpos := BstLean.Part212.latitudeCoefficient_pos (n := 12224) (p := 12) (by norm_num)
    (by norm_num) (mkR wr 0).1.2 hW.2.1
  have hval : BstLean.Part212.latitudeCoefficient 12224 12 (54 / 100) ≤ 54319 / 100000 := by
    norm_num [BstLean.Part212.latitudeCoefficient, BstLean.Part212.inverseLatitudeCoefficient]
  have hL12 := pow_le_pow_left₀ hpos.le (hmono.trans hval) 12
  obtain ⟨hLH, -, hwidth⟩ := bulk_of_window (by norm_num) (mkR wr 0) hW.2.1 hθ.1
    (by linarith [hθ.2])
  have hD0 : 0 ≤ nodeD (mkR wr 0) := by
    unfold nodeD Js
    have : 0 < nodeH (mkR wr 0) - nodeL (mkR wr 0) := by linarith
    positivity
  have hDP : DeltaP 12224 ≤ 13 / 10 ^ 9 := by
    have h : √(55 / 100 / (12224 : ℝ)) ≤ 671 / 100000 :=
      (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    unfold DeltaP
    norm_num only [Nat.cast_ofNat]
    linarith
  have hD := (hwidth.trans hDP)
  have hD12 : (nodeD (mkR wr 0) / (1 / 10000)) ^ 12 ≤ (13 / 10 ^ 5 : ℝ) ^ 12 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have e1 : (1 + 1 / 10000 : ℝ) ^ 12 * (54319 / 100000) ^ 12 +
      (1 + 1 / 10000 : ℝ) ^ 12 * (13 / 10 ^ 5) ^ 12 + 5 / 10 ^ 17 ≤ (5435 / 10000) ^ 12 := by
    norm_num
  have h1 := mul_le_mul_of_nonneg_left hL12 (by positivity : (0 : ℝ) ≤ (1 + 1 / 10000) ^ 12)
  have h2 := mul_le_mul_of_nonneg_left hD12 (by positivity : (0 : ℝ) ≤ (1 + 1 / 10000) ^ 12)
  linarith

end BstLean.Part276
