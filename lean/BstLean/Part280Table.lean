import BstLean.Part276Table

/-! Part 280, task 2 (first half): the sharp table event for every n in 11883–12224.

The guard is the World window with the M2 angle bound `θ ≤ .524`. The Lean World
packages give `θ ≤ noiseUpper n 2.02831`, which is at most .5234 from 11883
(`Part280Window`). Every statement here is generic in `n` with `11883 ≤ n`. -/
namespace BstLean.Part280
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223 BstLean.Part242
open BstLean.Part276 (fourA fourA_pos tableF tableW tableF_eq tableW_eq)

variable {n : ℕ}

/-- The M2 table guard: the World window and the angle bound `θ ≤ .524`. -/
def tightG (wr : WRet n) : Prop :=
  windowW wr ∧ BstLean.Part150.thetaC wr.2 (tau0p wr.1) ≤ 524 / 1000

theorem measurableSet_tightG : MeasurableSet {wr : WRet n | tightG wr} := by
  have ht : Measurable (fun wr : WRet n => tau0p wr.1) := measurable_tau0p.comp measurable_fst
  have hθ : Measurable (fun wr : WRet n => BstLean.Part150.thetaC wr.2 (tau0p wr.1)) := by
    unfold BstLean.Part150.thetaC
    exact ((ht.pow_const 2).const_mul _).div
      (((BstLean.Part150.measurable_rhoC (n := n)).comp (measurable_snd.prodMk ht)).pow_const 2)
  exact measurableSet_windowW.inter (measurableSet_le hθ measurable_const)

theorem tightW_of_tightG {wr : WRet n} (h : tightG wr) : BstLean.Part276.tightW wr :=
  ⟨h.1, by linarith [h.2]⟩

/-- The World window of the replacement theorem and the angle bound give the guard. -/
theorem tightG_of_window (hn : 1 ≤ n) (c : Ret n) (hW : WINDOW (paperDesignP n) c)
    (hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ≤ 524 / 1000) :
    tightG c.1 :=
  ⟨(BstLean.Part276.tightW_of_window hn c hW).1, hθ⟩

/-- The sharp table event at dimension `n` with the M2 guard and the paper allowances. -/
def sharpTableN (n : ℕ) : Set (Ret n) := {c | tightG c.1 →
  intF c ≤ tableF ^ 8 ∧ intW c ≤ tableW ^ 8}

theorem sharpTableN_measurable : MeasurableSet (sharpTableN n) := by
  have hw : MeasurableSet {c : Ret n | tightG c.1} :=
    measurableSet_tightG.preimage measurable_fst
  have hf := measurableSet_le (measurable_intF_comp (n := n) measurable_id)
    (measurable_const (a := tableF ^ 8))
  have he := measurableSet_le (measurable_intW_comp (n := n) measurable_id)
    (measurable_const (a := tableW ^ 8))
  have heq : sharpTableN n = {c : Ret n | tightG c.1}ᶜ ∪
      ({c : Ret n | intF c ≤ tableF ^ 8} ∩ {c : Ret n | intW c ≤ tableW ^ 8}) := by
    ext c
    simp only [sharpTableN, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : tightG c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

noncomputable def fourErrorN (c : Ret n) (i : Fin 4) (a : Ix n) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem fourErrorN_decomposition (c : Ret n) (a : Ix n) :
    fourErrorN c 0 a + fourErrorN c 1 a = exF c a ∧
    fourErrorN c 2 a + fourErrorN c 3 a = exW c a :=
  originalFour_decomposition c (gW c.1 a) (A2 c)

theorem sharpTableN_of_moments {c : Ret n}
    (h : ∀ i, MomentBound (muI n) (biasOrder i) (fourErrorN c i) (fourA i)) :
    c ∈ sharpTableN n := by
  have hb (i : Fin 4) : MomentBound (muI n) 8 (fourErrorN c i) (fourA i) :=
    (h i).lower (by norm_num) (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => fourErrorN c 0 a + fourErrorN c 1 a) = exF c :=
    funext fun a => (fourErrorN_decomposition c a).1
  have heW : (fun a => fourErrorN c 2 a + fourErrorN c 3 a) = exW c :=
    funext fun a => (fourErrorN_decomposition c a).2
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

noncomputable def nodeIndexN (hn : 1 ≤ n) (wr : WRet n) (a : Ix n) : Fin (Js n) :=
  ⟨gW wr a, gIdx_lt _ hn _⟩

theorem nodeIndexN_measurable (hn : 1 ≤ n) (wr : WRet n) :
    Measurable (nodeIndexN hn wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [nodeIndexN, gW, Fin.ext_iff]

noncomputable def nodeMeasureN (hn : 1 ≤ n) (wr : WRet n) : Measure (Fin (Js n)) :=
  (muI n).map (nodeIndexN hn wr)

theorem nodeMeasureN_mass (hn : 1 ≤ n) (wr : WRet n) : nodeMeasureN hn wr univ = 1 := by
  rw [nodeMeasureN, Measure.map_apply (nodeIndexN_measurable hn wr) MeasurableSet.univ]
  simp

theorem sharpTableN_of_second_layer_good (hn : 1 ≤ n) (c : Ret n)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (h : M ∉ ⋃ i, momentBad (nodeMeasureN hn c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourA i)) :
    withA2 c M ∈ sharpTableN n := by
  apply sharpTableN_of_moments
  intro i
  have hi : M ∉ momentBad (nodeMeasureN hn c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourA i) :=
    fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
  refine ⟨?_, (fourA_pos i).le, ?_⟩
  · have hf : fourErrorN (withA2 c M) i = (fun g : Fin (Js n) =>
        originalFourErrors c i g.val M) ∘ nodeIndexN hn c.1 := rfl
    rw [hf]
    exact (measurable_of_finite _).comp (nodeIndexN_measurable hn c.1)
  · change (∫⁻ a, ENNReal.ofReal (|originalFourErrors c i (gW c.1 a) M| ^ biasOrder i)
      ∂muI n) ≤ _
    have he : (∫⁻ a, ENNReal.ofReal (|originalFourErrors c i (gW c.1 a) M| ^ biasOrder i)
        ∂muI n) = ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
          ∂nodeMeasureN hn c.1 := by
      rw [nodeMeasureN, lintegral_map (measurable_of_finite _) (nodeIndexN_measurable hn c.1)]
      rfl
    rw [he]
    exact le_of_not_gt hi

theorem sharpTableN_bad_subset (hn : 1 ≤ n) (c : Ret n) :
    {M | withA2 c M ∉ sharpTableN n} ⊆
      ⋃ i, momentBad (nodeMeasureN hn c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourA i) := by
  intro M hM
  by_contra hg
  exact hM (sharpTableN_of_second_layer_good hn c M hg)

/-! ### Scalar facts from 11883 -/

theorem sqrt_bulk_ratio (hn : 11883 ≤ n) : √(55 / 100 / (n : ℝ)) ≤ 681 / 100000 := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  rw [div_le_iff₀ hx0]
  nlinarith

theorem bulk_radiusN (hn : 11883 ≤ n) : (63 / 100 : ℝ) ≤ √(qB n) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 := sqrt_bulk_ratio hn
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem bulk_positiveN (hn : 11883 ≤ n) : 0 < qB n := by
  have h := bulk_radiusN hn
  exact Real.sqrt_pos.mp (by linarith)

theorem deltaP_le (hn : 11883 ≤ n) : DeltaP n ≤ (14 / 10 ^ 9 : ℝ) := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have h := sqrt_bulk_ratio hn
  unfold DeltaP
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem latitude_key (x : ℝ) (hx : 11883 ≤ x) :
    (524 / 1000 : ℝ) / (1 - 50 * (524 / 1000) / x) * (x + 45) / x ≤ 52716 / 100000 := by
  have hx0 : 0 < x := by linarith
  have hd : 0 < 1 - 50 * (524 / 1000 : ℝ) / x := by
    rw [sub_pos, div_lt_one hx0]
    linarith
  rw [div_mul_eq_mul_div, div_div, div_le_iff₀ (mul_pos hd hx0)]
  have hdx : (1 - 50 * (524 / 1000 : ℝ) / x) * x = x - 131 / 5 := by
    rw [sub_mul, div_mul_cancel₀ _ hx0.ne']
    ring
  rw [hdx]
  linarith

theorem latitude_coefficient_le (hn : 11883 ≤ n) :
    BstLean.Part212.latitudeCoefficient n 12 (524 / 1000) ≤ 52716 / 100000 := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have h := latitude_key (n : ℝ) hx
  unfold BstLean.Part212.latitudeCoefficient BstLean.Part212.inverseLatitudeCoefficient
  calc _ = (524 / 1000 : ℝ) / (1 - 50 * (524 / 1000) / n) * (n + 45) / n := by
        push_cast
        ring
    _ ≤ _ := h

/-- The node geometry from 11883 under the M2 guard: `1 − s² ≤ .58`. -/
theorem node_geometryN (hn : 11883 ≤ n) {wr : WRet n} (hw : tightG wr)
    (θ : AHid n) {g : ℕ} (hg : g < Js n) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 58 / 100 := by
  let c := mkR wr θ
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by omega) c
    hw.1.1 hw.1.2.1 hw.1.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + (n : ℝ) * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (n : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (n : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos hx0 (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + (n : ℝ) * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      (n : ℝ) * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 524 / 1000 := hw.2
  rw [hθ] at hθU
  have hnb : (11883 : ℝ) * b ^ 2 ≤ (n : ℝ) * b ^ 2 :=
    mul_le_mul_of_nonneg_right hx (sq_nonneg b)
  have ha2 : 476 / 1000 ≤ a ^ 2 := by linarith
  have ha : 6899 / 10000 ≤ a := by nlinarith
  have hb : b ≤ 665 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 65 / 100 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB n := by
    have hr := bulk_radiusN hn
    have hr2 := Real.sq_sqrt (bulk_positiveN hn).le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB n)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

/-- The node order-twelve moment under the M2 guard: `H = .5275`. -/
theorem nodeMeasureN_moment12 (hn : 11883 ≤ n) {wr : WRet n} (hw : tightG wr) :
    ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂nodeMeasureN (by omega) wr ≤ ENNReal.ofReal ((5275 / 10000 : ℝ) ^ 12) := by
  have hn1 : 1 ≤ n := by omega
  have hW := BstLean.Part276.window_of_tightW hn1 (tightW_of_tightG hw) (0 : AHid n)
  rw [nodeMeasureN, lintegral_map (measurable_of_finite _) (nodeIndexN_measurable hn1 wr)]
  have hδ : (0 : ℝ) < 1 / 10000 := by norm_num
  have h := BstLean.Part276.node_latitude_moment12 (by omega) (mkR wr 0) hW hδ
  refine (le_of_eq_of_le ?_ h).trans (ENNReal.ofReal_le_ofReal ?_)
  · rfl
  have ht := BstLean.Part276.bulkTailMass_small (by omega) (mkR wr 0) hW
  have hθ := BstLean.Part276.window_theta hn1 (mkR wr 0) hW
  have hθ0 : (0 : ℝ) ≤ BstLean.Part150.thetaC (mkR wr 0).1.2
      ((paperDesignP n).tau0 (mkR wr 0)) := by
    have := hθ.1
    change (0 : ℝ) ≤ BstLean.Part150.thetaC (mkR wr 0).1.2 (tauR (mkR wr 0))
    linarith
  have hθ1 : BstLean.Part150.thetaC (mkR wr 0).1.2 ((paperDesignP n).tau0 (mkR wr 0)) ≤
      524 / 1000 := hw.2
  have hmono := BstLean.Part212.latitudeCoefficient_mono (n := n) (p := 12) (by norm_num)
    (by omega) hθ0 hθ1 (by norm_num)
  have hpos := BstLean.Part212.latitudeCoefficient_pos (n := n) (p := 12) (by norm_num)
    (by omega) (mkR wr 0).1.2 hW.2.1
  have hL12 := pow_le_pow_left₀ hpos.le (hmono.trans (latitude_coefficient_le hn)) 12
  obtain ⟨hLH, -, hwidth⟩ := bulk_of_window (by omega) (mkR wr 0) hW.2.1 hθ.1
    (by linarith [hθ.2])
  have hD := hwidth.trans (deltaP_le hn)
  have hD0 : 0 ≤ nodeD (mkR wr 0) := by
    unfold nodeD Js
    have : 0 < nodeH (mkR wr 0) - nodeL (mkR wr 0) := by linarith
    positivity
  have hD12 : (nodeD (mkR wr 0) / (1 / 10000)) ^ 12 ≤ (14 / 10 ^ 5 : ℝ) ^ 12 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have e1 : (1 + 1 / 10000 : ℝ) ^ 12 * (52716 / 100000) ^ 12 +
      (1 + 1 / 10000 : ℝ) ^ 12 * (14 / 10 ^ 5) ^ 12 + 5 / 10 ^ 17 ≤ (5275 / 10000) ^ 12 := by
    norm_num
  have h1 := mul_le_mul_of_nonneg_left hL12 (by positivity : (0 : ℝ) ≤ (1 + 1 / 10000) ^ 12)
  have h2 := mul_le_mul_of_nonneg_left hD12 (by positivity : (0 : ℝ) ≤ (1 + 1 / 10000) ^ 12)
  linarith

end BstLean.Part280
