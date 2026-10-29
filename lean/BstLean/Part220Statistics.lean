import BstLean.Part220Frame
import BstLean.Part220Events

/-! A weighted first-layer event uses fixed order64 at every dimension from four. -/
namespace BstLean.Part220
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part172
open BstLean.Part170 (mkR tA)
open BstLean.Part161 (uHat xLat)
open BstLean.Part53 (unitF53)

noncomputable def statisticsField {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3) :
    Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ :=
  ![F1 wr, F2 wr g, F3 wr g] i

theorem statisticsField_measurable {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3) :
    Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      statisticsField wr g i p.1 p.2) := by
  fin_cases i
  · exact (fr_meas_e1 wr).comp measurable_fst
  · exact (fr_meas_e2 wr g).comp measurable_fst
  · exact gd_F3_meas wr g

theorem statisticsField_bound {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (v : Fin (n - 1) → ℝ) :
    normSq (statisticsField wr g i A v) ≤ tA n := by
  fin_cases i
  · exact e1v_normSq_le _
  · exact e2v_normSq_le _ _
  · exact gd_F3_le wr g A v

theorem statisticsField_admissible {n : ℕ} (hn : 2 ≤ n) (wr : WRet n)
    (hc : wr.2 ≠ 0) (g : ℕ) (i : Fin 3) (v : Fin (n - 1) → ℝ) :
    fr_Adm (xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v))
      (uHat (mkR wr (0, 0))) (fun A => statisticsField wr g i A v) := by
  fin_cases i
  · exact e1v_adm _ _
  · exact e2v_adm hn _ hc g _
  · intro A A' hx hu hr
    have h := cdir_adm hn (mkR wr (0, 0)) hc (nodeS (mkR wr (0, 0)) g)
      (xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)) A A' hx hu hr
    exact congrArg (fun z => sqrt (tA n) • z) h

/-- Integrating nodes adds no union charge over nodes. -/
theorem weighted_statistics_moment64 {n q J : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (wr : WRet n) (hc : wr.2 ≠ 0) (ν : Measure (Fin J))
    (node : Fin J → ℕ) (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    {H : ℝ} (hH : 0 ≤ H)
    (h64 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) (node g) ^ 2) ^ 64)
      ∂ν ≤ ENNReal.ofReal (H ^ 64)) (i : Fin 3) :
    ∫⁻ g, ∫⁻ v, ∫⁻ A, ENNReal.ofReal
      (|Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) (node g))
        (statisticsField wr (node g) i) A v| ^ 64)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ∂stdGauss (Fin (n - 1)) ∂ν ≤
      ENNReal.ofReal ((fr_X n q (tA n) * H) ^ 64) := by
  have hX := first_layer_constant_nonneg (q := q) hn (tA_nonneg n)
  refine (lintegral_mono fun g => first_layer_moment64 hn hq _ hc (hs g)
    (statisticsField wr (node g) i) (statisticsField_measurable wr (node g) i)
    (statisticsField_admissible (by omega) wr hc (node g) i)
    (tA_nonneg n) (statisticsField_bound wr (node g) i)).trans ?_
  simp_rw [mul_pow, mul_comm ((1 - _) ^ 64) (fr_X n q (tA n) ^ 64),
    ENNReal.ofReal_mul (pow_nonneg hX 64)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl h64).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (pow_nonneg hX 64), ← mul_pow]

theorem statisticsTf_measurable {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3) :
    Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g)
        (statisticsField wr g i) p.1 p.2) := by
  exact mk_meas_Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g)
    (F := statisticsField wr g i) (statisticsField_measurable wr g i)

noncomputable def statisticsNodeFunction {n J : ℕ} (wr : WRet n) (node : Fin J → ℕ)
    (i : Fin 3) (p : Fin J ×
      (Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ))) : ℝ :=
  Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) (node p.1))
    (statisticsField wr (node p.1) i) p.2.1 p.2.2

theorem statisticsNode_measurable {n J : ℕ} (wr : WRet n) (node : Fin J → ℕ)
    (i : Fin 3) : Measurable (statisticsNodeFunction wr node i) :=
  measurable_from_prod_countable_right (fun g => statisticsTf_measurable wr (node g) i)

def statisticsReorder {n J : ℕ} (p : (Fin J × (Fin (n - 1) → ℝ)) ×
      Matrix (Fin (mA n)) (Fin n) ℝ) : Fin J ×
      (Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ)) :=
  (p.1.1, (p.2, p.1.2))

/-- The node and latitude distribution stays fixed when the first layer is drawn. -/
noncomputable def statisticsError {n J : ℕ} (wr : WRet n) (node : Fin J → ℕ)
    (i : Fin 3) : (Fin J × (Fin (n - 1) → ℝ)) →
      Matrix (Fin (mA n)) (Fin n) ℝ → ℝ :=
  Function.curry (statisticsNodeFunction wr node i ∘ statisticsReorder (n := n) (J := J))

theorem statisticsReorder_measurable {n J : ℕ} :
    Measurable (statisticsReorder (n := n) (J := J)) := by
  exact (measurable_fst.comp measurable_fst).prodMk
    (measurable_snd.prodMk (measurable_snd.comp measurable_fst))

theorem statisticsError_measurable {n J : ℕ} (wr : WRet n) (node : Fin J → ℕ)
    (i : Fin 3) : Measurable (Function.uncurry (statisticsError wr node i)) :=
  (statisticsNode_measurable wr node i).comp (statisticsReorder_measurable (n := n) (J := J))


/-- The three actual bounded direction fields have one weighted first-layer payment.
This event concerns `Tf`; it does not identify the paper's energy-weighted field. -/
theorem weighted_statistics_charge64 {n q J : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (wr : WRet n) (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) [SFinite ν]
    (node : Fin J → ℕ) (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    {H C : ℝ} (hH : 0 ≤ H) (hC : 0 < C)
    (h64 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) (node g) ^ 2) ^ 64)
      ∂ν ≤ ENNReal.ofReal (H ^ 64)) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      (⋃ i, momentBad (ν.prod (stdGauss (Fin (n - 1)))) (statisticsError wr node i) 64 C) ≤
        3 * (fr_X n q (tA n) * H / C) ^ 64 := by
  apply three_statistics_markov _ _ (statisticsError wr node)
    (mul_nonneg (first_layer_constant_nonneg hn (tA_nonneg n)) hH) hC
    (statisticsError_measurable wr node)
  intro i
  have hm := ((statisticsError_measurable wr node i).abs.pow_const 64).ennreal_ofReal
  have hf : Measurable (fun p : Fin J × (Fin (n - 1) → ℝ) =>
      ∫⁻ A, ENNReal.ofReal (|statisticsError wr node i p A| ^ 64)
        ∂gaussMat (mA n) n (2 / (n : ℝ))) := hm.lintegral_prod_right'
  have hp := lintegral_prod (ν := stdGauss (Fin (n - 1))) (μ := ν) _ hf.aemeasurable
  rw [hp]
  exact weighted_statistics_moment64 hn hq wr hc ν node hs hH h64 i

#print axioms statisticsField_admissible
#print axioms weighted_statistics_moment64
#print axioms weighted_statistics_charge64
end BstLean.Part220
