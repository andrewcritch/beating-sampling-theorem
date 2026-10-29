import BstLean.Part292Charge
import BstLean.Part292Geometry

/-! The four good moments supply the actual integrated exact-rule table errors. -/
namespace BstLean.Part292
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def lowTableF : ℝ := tableAllowance 0+tableAllowance 1
noncomputable def lowTableW : ℝ := tableAllowance 2+tableAllowance 3

def tableCore {n : ℕ} (c : Ret n) : Prop := intF c ≤ lowTableF^8 ∧ intW c ≤ lowTableW^8

theorem tableCore_measurable {n : ℕ} : MeasurableSet {c : Ret n | tableCore c} :=
  (measurableSet_le (measurable_intF_comp measurable_id) measurable_const).inter
    (measurableSet_le (measurable_intW_comp measurable_id) measurable_const)

theorem finite_node_integrable {n : ℕ} (hn : 1 ≤ n) (wr : WRet n)
    (f : Fin (Js n) → ℝ) :
    Integrable (fun a => f (BstLean.Part280.nodeIndexN hn wr a)) (muI n) := by
  let ν := BstLean.Part280.nodeMeasureN hn wr
  haveI : IsFiniteMeasure ν := by dsimp [ν, BstLean.Part280.nodeMeasureN]; infer_instance
  have hi : Integrable f ν := by
    refine (integrable_const (∑ g, |f g|)).mono' (measurable_of_finite f).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_univ g)
  exact (integrable_map_measure (measurable_of_finite f).aestronglyMeasurable
    (BstLean.Part280.nodeIndexN_measurable hn wr).aemeasurable).mp hi

theorem exact_table_pow_integrable {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (k : ℕ) :
    Integrable (fun a => exF c a^k) (muI n) ∧ Integrable (fun a => exW c a^k) (muI n) :=
  ⟨finite_node_integrable hn c.1 (fun g => exFn c g.val^k),
    finite_node_integrable hn c.1 (fun g => exWn c g.val^k)⟩

theorem fourErrorN_moment_pullback {n : ℕ} (hn : 1 ≤ n) (c : Ret n)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (i : Fin 4) {k : ℕ} {B : ℝ}
    (h : MomentBound (BstLean.Part280.nodeMeasureN hn c.1) k
      (fun g => originalFourErrors c i g.val M) B) :
    MomentBound (muI n) k (BstLean.Part280.fourErrorN (withA2 c M) i) B := by
  have hf : BstLean.Part280.fourErrorN (withA2 c M) i =
      (fun g : Fin (Js n) => originalFourErrors c i g.val M) ∘
        BstLean.Part280.nodeIndexN hn c.1 := rfl
  rw [hf]
  refine ⟨h.measurable.comp (BstLean.Part280.nodeIndexN_measurable hn c.1), h.nonneg, ?_⟩
  have hh := h.moment
  rw [BstLean.Part280.nodeMeasureN, lintegral_map (measurable_of_finite _)
    (BstLean.Part280.nodeIndexN_measurable hn c.1)] at hh
  exact hh

theorem tableCore_of_four_moments {n : ℕ} (c : Ret n)
    (h : ∀ i, MomentBound (muI n) 8 (BstLean.Part280.fourErrorN c i) (tableAllowance i)) :
    tableCore c := by
  have hF := (h 0).add (by norm_num) (h 1)
  have hW := (h 2).add (by norm_num) (h 3)
  have heF : (fun a => BstLean.Part280.fourErrorN c 0 a+
      BstLean.Part280.fourErrorN c 1 a) = exF c :=
    funext fun a => (BstLean.Part280.fourErrorN_decomposition _ a).1
  have heW : (fun a => BstLean.Part280.fourErrorN c 2 a+
      BstLean.Part280.fourErrorN c 3 a) = exW c :=
    funext fun a => (BstLean.Part280.fourErrorN_decomposition _ a).2
  rw [heF] at hF
  rw [heW] at hW
  have hf := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hw := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  exact ⟨by simpa only [intF, lowTableF, ← pow_mul, show (4*2 : ℕ) = 8 from rfl] using hf.2,
    by simpa only [intW, lowTableW, ← pow_mul, show (4*2 : ℕ) = 8 from rfl] using hw.2⟩


theorem tableCore_of_second_good {n : ℕ} (hn : 1 ≤ n) (c : Ret n)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (h : M ∉ tableBad (BstLean.Part280.nodeMeasureN hn c.1)
      (fun i g => originalFourErrors c i g.val)) : tableCore (withA2 c M) := by
  apply tableCore_of_four_moments
  intro i
  apply fourErrorN_moment_pullback hn c M i
  exact table_moments_on_good (BstLean.Part280.nodeMeasureN hn c.1)
    (BstLean.Part280.nodeMeasureN_mass hn c.1).le
    (fun i g => originalFourErrors c i g.val) (fun _ _ => measurable_of_finite _) h i

end BstLean.Part292
