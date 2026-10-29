import BstLean.Part293Quadrature
import BstLean.Part252Table
import BstLean.Part170Ev
import BstLean.Part242Norm

/-! Exact table moments, grid prices and finite-rule prices give the two stored-error norms. -/
namespace BstLean.Part293
open Real MeasureTheory Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part242 BstLean.Part252
open BstLean.Part150 (c1F c2F)

structure StoredInputs {n : ℕ} (c : Ret n) (K : Set (Ix n)) (aw af : ℝ) where
  O1 : ℝ
  O2 : ℝ
  q : ℝ
  sigma : ℝ
  tableF : ℝ
  tableW : ℝ
  gridF : ℝ
  gridW : ℝ
  ruleF : ℝ
  ruleW : ℝ
  O1_pos : 0 < O1
  O2_pos : 0 < O2
  q_pos : 0 < q
  sigma_pos : 0 < sigma
  tableF_pos : 0 < tableF
  tableW_pos : 0 < tableW
  first_operator : OpB (A1 c) O1
  second_operator : OpB (A2 c) O2
  kept_measurable : MeasurableSet K
  kept_bulk : K ⊆ bulkIx (paperDesignP n) c
  node_separation : nodeL c < nodeH c
  node_bulk : ∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - q
  node_variance : ∀ a ∈ K, vsig2 c (sgR c a) ≤ sigma ^ 2
  exact_location : intF c ≤ tableF ^ 8
  exact_energy : intW c ≤ tableW ^ 8
  grid_location : (n : ℝ) * (O2 * O1 * (nodeD c / 2) / (√(n : ℝ) * √q)) ≤ gridF
  grid_energy : (n : ℝ) * (2 * (O2 * O1) ^ 2 * (nodeD c / 2) / (n * √q)) ≤ gridW
  rule_location : (n : ℝ) * (√(n : ℝ) * ((19 / 100) * sigma / Jz n)) ≤ ruleF
  rule_energy : (n : ℝ) * (n * ((9 / 100) * sigma ^ 2 / Jz n)) ≤ ruleW
  location_total : tableF + gridF + ruleF ≤ af
  energy_total : tableW + gridW + ruleW ≤ aw

theorem eighth_norm_of_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℝ} (hf : Measurable f) {a : ℝ} (ha : 0 ≤ a)
    (hi : Integrable (fun x => f x ^ 8) μ) (hb : ∫ x, f x ^ 8 ∂μ ≤ a ^ 8) :
    LBound μ 8 f a := by
  apply LBound.ofMoment (by norm_num : (8 : ℕ) ≠ 0)
  refine ⟨hf, ha, ?_⟩
  have he : (fun x => |f x| ^ 8) = fun x => f x ^ 8 := by
    funext x
    exact (Even.pow_abs (by norm_num : Even (8 : ℕ)) (f x))
  simp_rw [show ∀ x, |f x| ^ 8 = f x ^ 8 from fun x => congrFun he x]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by positivity)]
  exact ENNReal.ofReal_le_ofReal hb

theorem stored_norms_of_table {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    {K : Set (Ix n)} {aw af : ℝ} (S : StoredInputs c K aw af) :
    LBound ((muI n).restrict K) 8 (fun a => (n : ℝ) * (wbR c a - wtR c a)) aw ∧
    LBound ((muI n).restrict K) 8 (fun a => (n : ℝ) * (fbR c a - ftR c a)) af := by
  obtain ⟨MF, bF⟩ := bdd_exF (by omega) c
  obtain ⟨MW, bW⟩ := bdd_exW (by omega) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8) (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8) (bdd_pow bW 8) K
  have iFu := intOn_of_bdd ((measurable_exF c).pow_const 8) (bdd_pow bF 8) univ
  have iWu := intOn_of_bdd ((measurable_exW c).pow_const 8) (bdd_pow bW 8) univ
  rw [integrableOn_univ] at iFu iWu
  have hF := (setIntegral_le_integral (s := K) iFu
    (ae_of_all _ fun a => by positivity)).trans S.exact_location
  have hW := (setIntegral_le_integral (s := K) iWu
    (ae_of_all _ fun a => by positivity)).trans S.exact_energy
  have hf := location_error_of_exact (by omega) c S.kept_measurable S.kept_bulk
    S.first_operator S.second_operator S.O1_pos S.O2_pos S.q_pos S.sigma_pos
    S.node_separation S.node_bulk S.node_variance S.tableF_pos iF hF
  have hw := energy_error_of_exact (by omega) c S.kept_measurable S.kept_bulk
    S.first_operator S.second_operator S.O1_pos S.O2_pos S.q_pos S.sigma_pos
    S.node_separation S.node_bulk S.node_variance S.tableW_pos iW hW
  have hc := finite_rule_constants_band hn
  have hSigma := S.sigma_pos.le
  have hrF : (n : ℝ) * (√(n : ℝ) *
      (c1F (exp (1 / 2) / 12) (Jz n) * S.sigma / Jz n)) ≤ S.ruleF := by
    apply le_trans _ S.rule_location
    gcongr
    exact hc.1
  have hrW : (n : ℝ) * (n *
      (c2F (exp (1 / 2) / 12) (Jz n) * S.sigma ^ 2 / Jz n)) ≤ S.ruleW := by
    apply le_trans _ S.rule_energy
    gcongr
    exact hc.2
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (sub_pos.mpr S.node_separation) (by positivity)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz n)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz n)
  have hO1 := S.O1_pos.le
  have hO2 := S.O2_pos.le
  have hs := S.sigma_pos.le
  have hTF := S.tableF_pos.le
  have hTW := S.tableW_pos.le
  have hgF := S.grid_location
  have hgW := S.grid_energy
  have htotF := S.location_total
  have htotW := S.energy_total
  have hgF0 : 0 ≤ S.gridF :=
    (show 0 ≤ (n : ℝ) * (S.O2 * S.O1 * (nodeD c / 2) /
      (√(n : ℝ) * √S.q)) by positivity).trans hgF
  have hgW0 : 0 ≤ S.gridW :=
    (show 0 ≤ (n : ℝ) * (2 * (S.O2 * S.O1) ^ 2 * (nodeD c / 2) /
      (n * √S.q)) by positivity).trans hgW
  have hrF0 : 0 ≤ S.ruleF :=
    (show 0 ≤ (n : ℝ) * (√(n : ℝ) *
      (c1F (exp (1 / 2) / 12) (Jz n) * S.sigma / Jz n)) by positivity).trans hrF
  have hrW0 : 0 ≤ S.ruleW :=
    (show 0 ≤ (n : ℝ) * (n *
      (c2F (exp (1 / 2) / 12) (Jz n) * S.sigma ^ 2 / Jz n)) by positivity).trans hrW
  constructor
  · apply eighth_norm_of_integral _ (((measurable_wbR c).sub (measurable_wtR c)).const_mul _)
      (le_trans (by positivity) S.energy_total) hw.1
    exact hw.2.trans (pow_le_pow_left₀ (by positivity) (by linarith) 8)
  · apply eighth_norm_of_integral _ (((measurable_fbR c).sub (measurable_ftR c)).const_mul _)
      (le_trans (by positivity) S.location_total) hf.1
    exact hf.2.trans (pow_le_pow_left₀ (by positivity) (by linarith) 8)

end BstLean.Part293

/-- info: 'BstLean.Part293.stored_norms_of_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.stored_norms_of_table
