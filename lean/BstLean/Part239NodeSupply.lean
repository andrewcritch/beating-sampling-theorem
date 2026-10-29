import BstLean.Part223MomentBounds
import BstLean.Part239StatisticNorm
import BstLean.Part223StatisticNorm

/-! The weighted statistics event supplies integrated scalar bounds. -/
namespace BstLean.Part239
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (mkR)

open BstLean.Part223 (MomentBound)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem paperStatistics_momentBound {n J : ℕ} (hn : 1 ≤ n) (wr : WRet n)
    (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O C : ℝ} (hOp : OpB A O) (hC : 0 ≤ C)
    (hE : A ∈ paperStatisticsEvent wr ν node C) (i : Fin 3) :
    MomentBound ν 416 (fun g => paperNodeStatistic wr (node g) i A) C := by
  refine ⟨measurable_of_countable _, hC, ?_⟩
  simpa only [abs_of_nonneg (paperNodeStatistic_nonneg _ _ _ _)] using
    paperStatisticsEvent_real hn wr hc ν node hs A hOp hE i


#print axioms paperStatistics_momentBound

lemma moment_mul208 {f g : X → ℝ} {A B : ℝ}
    (hf : MomentBound μ 416 f A) (hg : MomentBound μ 416 g B) :
    MomentBound μ 208 (fun x => f x * g x) (A * B) := by
  haveI : ENNReal.HolderTriple (416 : ℝ≥0∞) 416 208 := by
    constructor
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]
  have h := eLpNorm_smul_le_mul_eLpNorm (μ := μ) (p := (416 : ℝ≥0∞))
    (q := (416 : ℝ≥0∞)) (r := (208 : ℝ≥0∞))
      hf.measurable.aestronglyMeasurable hg.measurable.aestronglyMeasurable
  have hn : eLpNorm (fun x => f x * g x) 208 μ ≤ ENNReal.ofReal (A * B) := by
    refine h.trans ?_
    rw [ENNReal.ofReal_mul hf.nonneg]
    exact mul_le_mul' (BstLean.Part213.moment_norm_bound hf.measurable
      (by norm_num) hf.nonneg hf.moment)
      (BstLean.Part213.moment_norm_bound hg.measurable (by norm_num) hg.nonneg hg.moment)
  have hp := pow_le_pow_left' hn 208
  have he : eLpNorm (fun x => f x * g x) (208 : ℝ≥0∞) μ ^ (208 : ℕ) =
      ∫⁻ x, ENNReal.ofReal (|f x * g x| ^ 208) ∂μ := by
    exact BstLean.Part153.eLpNorm_nat_pow (μ := μ) (f := fun x => f x * g x)
      (by norm_num : (208 : ℕ) ≠ 0) (hf.measurable.mul hg.measurable).aestronglyMeasurable
  rw [he, ← ENNReal.ofReal_pow (mul_nonneg hf.nonneg hg.nonneg)] at hp
  exact ⟨hf.measurable.mul hg.measurable, mul_nonneg hf.nonneg hg.nonneg, hp⟩


lemma moment_mul104 {f g : X → ℝ} {A B : ℝ}
    (hf : MomentBound μ 208 f A) (hg : MomentBound μ 208 g B) :
    MomentBound μ 104 (fun x => f x * g x) (A * B) := by
  haveI : ENNReal.HolderTriple (208 : ℝ≥0∞) 208 104 := by
    constructor
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]
  have h := eLpNorm_smul_le_mul_eLpNorm (μ := μ) (p := (208 : ℝ≥0∞))
    (q := (208 : ℝ≥0∞)) (r := (104 : ℝ≥0∞))
      hf.measurable.aestronglyMeasurable hg.measurable.aestronglyMeasurable
  have hn : eLpNorm (fun x => f x * g x) 104 μ ≤ ENNReal.ofReal (A * B) := by
    refine h.trans ?_
    rw [ENNReal.ofReal_mul hf.nonneg]
    exact mul_le_mul' (BstLean.Part213.moment_norm_bound hf.measurable
      (by norm_num) hf.nonneg hf.moment)
      (BstLean.Part213.moment_norm_bound hg.measurable (by norm_num) hg.nonneg hg.moment)
  have hp := pow_le_pow_left' hn 104
  have he : eLpNorm (fun x => f x * g x) (104 : ℝ≥0∞) μ ^ (104 : ℕ) =
      ∫⁻ x, ENNReal.ofReal (|f x * g x| ^ 104) ∂μ := by
    exact BstLean.Part153.eLpNorm_nat_pow (μ := μ) (f := fun x => f x * g x)
      (by norm_num : (104 : ℕ) ≠ 0) (hf.measurable.mul hg.measurable).aestronglyMeasurable
  rw [he, ← ENNReal.ofReal_pow (mul_nonneg hf.nonneg hg.nonneg)] at hp
  exact ⟨hf.measurable.mul hg.measurable, mul_nonneg hf.nonneg hg.nonneg, hp⟩



/-- Four coefficient factors use the node order416 on the same node measure. -/
theorem degree_four_moment104 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g h j : X → ℝ} {A B C D : ℝ}
    (hf : BstLean.Part223.MomentBound μ 416 f A)
    (hg : BstLean.Part223.MomentBound μ 416 g B)
    (hh : BstLean.Part223.MomentBound μ 416 h C)
    (hj : BstLean.Part223.MomentBound μ 416 j D) :
    BstLean.Part223.MomentBound μ 104 (fun x => (f x * g x) * (h x * j x))
      ((A * B) * (C * D)) :=
  moment_mul104 (moment_mul208 hf hg) (moment_mul208 hh hj)

/-- The actual scalar variance and exceptional formulas consume node order416. -/
theorem scalar_statistics_moments104 (hmass : μ Set.univ ≤ 1)
    {M₁ M₂ M₃ : X → ℝ} {C a b e : ℝ}
    (h1 : MomentBound μ 416 M₁ C) (h2 : MomentBound μ 416 M₂ C)
    (h3 : MomentBound μ 416 M₃ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) :
    MomentBound μ 104 (fun x => a * (M₁ x + M₂ x)) (a * (C + C)) ∧
    MomentBound μ 104 (fun x => b * M₃ x + (a * (M₁ x + M₂ x)) ^ 2)
      (b * C + (a * (C + C)) ^ 2) ∧
    MomentBound μ 104 (fun x => e * M₃ x ^ 4) (e * C ^ 4) := by
  have hD := (h1.add (by norm_num) h2).scale ha
  have hV := ((h3.lower (by norm_num : 1 ≤ 104) (by norm_num) hmass).scale hb).add
    (by norm_num) ((hD.lower (by norm_num : 1 ≤ 208) (by norm_num) hmass).power
      (k := 104) (r := 2))
  exact ⟨hD.lower (by norm_num) (by norm_num) hmass, hV,
    (h3.power (k := 104) (r := 4)).scale he⟩

lemma paperNodeStatistic_eq_original {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) :
    paperNodeStatistic wr g i A = BstLean.Part223.paperNodeStatistic wr g i A := rfl

/-- The new event supplies the existing real node statistic at order416. -/
theorem paperStatistics_momentBound_original {n J : ℕ} (hn : 1 ≤ n) (wr : WRet n)
    (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O C : ℝ} (hOp : OpB A O) (hC : 0 ≤ C)
    (hE : A ∈ paperStatisticsEvent wr ν node C) (i : Fin 3) :
    MomentBound ν 416 (fun g => BstLean.Part223.paperNodeStatistic wr (node g) i A) C := by
  simpa only [paperNodeStatistic_eq_original] using
    paperStatistics_momentBound hn wr hc ν node hs A hOp hC hE i

def node416Event {n J : ℕ} (wr : WRet n) (ν : Measure (Fin J))
    (node : Fin J → ℕ) (C : ℝ) : Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {A | ∀ i : Fin 3,
    MomentBound ν 416 (fun g => BstLean.Part223.paperNodeStatistic wr (node g) i A) C}

/-- The operator bound used for integrability is available for each finite matrix. -/
theorem node416Event_eq {n J : ℕ} (hn : 1 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (ν : Measure (Fin J)) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1) {C : ℝ} (hC : 0 ≤ C) :
    node416Event wr ν node C = paperStatisticsEvent wr ν node C := by
  ext A
  have hOp := BstLean.Part169.opB_of_opN A le_rfl
  constructor
  · intro hA i
    have h := (hA i).moment
    simp only [abs_of_nonneg (BstLean.Part223.paperNodeStatistic_nonneg _ _ _ _)] at h
    simp_rw [← paperNodeStatistic_eq_original,
      paperNodeStatistic_pow416 hn wr hc _ (hs _) i A hOp] at h
    exact h
  · intro hA i
    exact paperStatistics_momentBound_original hn wr hc ν node hs A hOp hC hA i

theorem node416Event_measurable {n J : ℕ} (hn : 1 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (ν : Measure (Fin J)) [SFinite ν] (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1) {C : ℝ} (hC : 0 ≤ C) :
    MeasurableSet (node416Event wr ν node C) := by
  rw [node416Event_eq hn wr hc ν node hs hC]
  exact paperStatisticsEvent_measurable wr ν node C

/-- The three existing node statistics have one charge of one ten-thousandth. -/
theorem node416_charge {n q J : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (wr : WRet n) (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) [SFinite ν]
    (hmass : ν Set.univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      (node416Event wr ν node (statisticsConstant (paperStatisticsBound n q)))ᶜ ≤
      1 / 10000 := by
  rw [node416Event_eq (by omega) wr hc ν node hs
    (statisticsConstant_pos (paperStatisticsBound_pos hn hq)).le]
  exact paperStatistics_oneTenThousand hn hq wr hc ν hmass node hs

#print axioms moment_mul104
#print axioms degree_four_moment104
#print axioms scalar_statistics_moments104
#print axioms paperNodeStatistic_eq_original
#print axioms paperStatistics_momentBound_original
#print axioms node416Event_eq
#print axioms node416_charge

theorem scalar_root_product104 {D V : X → ℝ} {d v : ℝ}
    (hD : MomentBound μ 104 D d) (hV : MomentBound μ 104 V v)
    (hD0 : ∀ x, 0 ≤ D x) (hV0 : ∀ x, 0 ≤ V x) :
    MomentBound μ 104 (fun x => sqrt (D x) * sqrt (V x)) (sqrt d * sqrt v) :=
  moment_mul104 (hD.sqrt hD0) (hV.sqrt hV0)

/-- The installed row coefficients preserve the integrated statistics bounds. -/
theorem row_coefficients_moments104 {D H V P : X → ℝ} {d h v p sm Γ C sp : ℝ}
    (hD : MomentBound μ 104 D d) (hH : MomentBound μ 104 H h)
    (hV : MomentBound μ 104 V v) (hP : MomentBound μ 104 P p)
    (hD0 : ∀ x, 0 ≤ D x) (hV0 : ∀ x, 0 ≤ V x)
    (hsm : 0 ≤ sm) (hΓ : 0 ≤ Γ) (hC : 0 ≤ C) (hsp : 0 ≤ sp) :
    MomentBound μ 104 (fun x => AF0 sm Γ (H x) (V x) (P x)) (AF0 sm Γ h v p) ∧
    MomentBound μ 104 (fun x => AF1 sm (D x) (V x) (P x) C) (AF1 sm d v p C) ∧
    MomentBound μ 104 (fun x => AF2 sm (D x)) (AF2 sm d) ∧
    MomentBound μ 104 (fun x => AW0 sm Γ (H x) (V x) (P x)) (AW0 sm Γ h v p) ∧
    MomentBound μ 104 (fun x => AW1 sm sp (D x) (V x) (P x) C) (AW1 sm sp d v p C) ∧
    MomentBound μ 104 (fun x => AW2 (D x) (P x) C) (AW2 d p C) := by
  have hp0 := (BstLean.Part153.phiG_pos 0).le
  have hp1 := (BstLean.Part153.phiG_pos 1).le
  have hroot := scalar_root_product104 hD hV hD0 hV0
  have h0 := ((hH.scale (by positivity : 0 ≤ BstLean.Part153.phiG 0 / (2 * sm))).add
    (by norm_num) (hV.scale (by positivity :
      0 ≤ (1 / 2 : ℝ) * (BstLean.Part153.phiG 0 / (sqrt 2 * sm ^ 3))))).add
        (by norm_num) (hP.scale (by positivity :
          0 ≤ (3 / 2 : ℝ) * BstLean.Part153.phiG 0 / sm * Γ))
  have h1 := (hroot.scale (by positivity :
      0 ≤ (1 / 2 : ℝ) * (2 * BstLean.Part153.phiG 1 / sm ^ 2))).add
    (by norm_num) (hP.scale (by positivity : 0 ≤ 2 * (2 * sqrt 2 * C)))
  have h2 := hD.scale (by positivity :
    0 ≤ (1 / 2 : ℝ) * (sqrt 2 * BstLean.Part153.phiG 0 / sm))
  have hw0 := (hH.add (by norm_num)
    (hV.scale (by positivity : 0 ≤ BstLean.Part153.phiG 1 / (2 * sm ^ 2)))).add
      (by norm_num) (hP.scale (by positivity : 0 ≤ 4 * Γ))
  have hw1 := (hroot.scale (by positivity : 0 ≤ sqrt 2 * BstLean.Part153.phiG 0 / sm)).add
    (by norm_num) (hP.scale (by positivity : 0 ≤ 4 * sqrt 2 * C * sp))
  have hw2 := hD.add (by norm_num) (hP.scale (by positivity : 0 ≤ 28 * C ^ 2))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert h0 using 1 <;> unfold AF0 <;> first | (funext x; ring) | ring
  · convert h1 using 1 <;> unfold AF1 <;> first | (funext x; ring) | ring
  · convert h2 using 1 <;> unfold AF2 <;> first | (funext x; ring) | ring
  · convert hw0 using 1 <;> unfold AW0 <;> first | (funext x; ring) | ring
  · convert hw1 using 1 <;> unfold AW1 <;> first | (funext x; ring) | ring
  · convert hw2 using 1 <;> unfold AW2 <;> first | (funext x; ring) | ring


#print axioms row_coefficients_moments104
end BstLean.Part239
