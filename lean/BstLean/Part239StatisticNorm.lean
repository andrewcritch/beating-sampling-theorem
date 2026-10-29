import BstLean.Part239Event

/-! Finite latitude norms for the three statistics in the weighted event. -/
namespace BstLean.Part239
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part172
open BstLean.Part170 (mkR tA)
open BstLean.Part161 (uHat xLat momN)
open BstLean.Part162 (dirW)
open BstLean.Part167 (latSq D1A1)
open BstLean.Part53 (unitF53)
open BstLean.Part220

lemma statisticsTf_eq_paperPsi {n : ℕ} (hn : 1 ≤ n) (wr : WRet n) (g : ℕ)
    (i : Fin 3) (A : Matrix (Fin (mA n)) (Fin n) ℝ) (v : Fin (n - 1) → ℝ) :
    Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (statisticsField wr g i) A v =
      (1 - nodeS (mkR wr (0, 0)) g ^ 2) * tA n * paperPsi wr g i A v := by
  have ht : 0 < tA n := by
    unfold tA mA
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  unfold Tf paperPsi paperDirection
  rw [smul_vecMul, BstLean.Part167.latSq_smul, inv_pow, sq_sqrt ht.le]
  field_simp

lemma paperPsi_bounded {n : ℕ} (hn : 1 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (i : Fin 3) (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (v : Fin (n - 1) → ℝ) :
    |paperPsi wr g i A v| ≤ 3 * (∑ j, ∑ k, A j k ^ 2) := by
  have hd := paperDirection_bound hn wr g i A v
  have hg := (mk_vecMul_le (paperDirection wr g i A v)
    (D1A1 A (xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)))).trans
      (mul_le_mul hd (mk_D1A1_le A _) (by positivity) (by norm_num : (0 : ℝ) ≤ 1))
  simp only [one_mul] at hg
  have hlat := mk_latSq_abs
    (vecMul (paperDirection wr g i A v)
      (D1A1 A (xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v))))
    (uHat (mkR wr (0, 0))) (dirW (mkR wr (0, 0)) (unitF53 v))
  rw [BstLean.Part161.normSq_uHat hc] at hlat
  have hw := mk_dirW_le hn (mkR wr (0, 0)) v
  have hw0 := normSq_nonneg (dirW (mkR wr (0, 0)) (unitF53 v))
  refine hlat.trans ?_
  calc
    _ ≤ (∑ j, ∑ k, A j k ^ 2) * 3 := by gcongr <;> linarith
    _ = _ := by ring

lemma activationWeight_bounded {n : ℕ} (hn : 1 ≤ n) (wr : WRet n) (g : ℕ)
    (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O : ℝ} (hOp : OpB A O)
    (v : Fin (n - 1) → ℝ) :
    |activationWeight wr g A v| ≤ ((n : ℝ) * tA n / 2) * O ^ 2 := by
  have hk : 0 ≤ (n : ℝ) * tA n / 2 := by have := tA_nonneg n; positivity
  have hact := BstLean.Part170.aLat_normSq_le hn (mkR wr (A, 0)) hs hOp v
  unfold activationWeight
  rw [abs_of_nonneg (mul_nonneg hk (normSq_nonneg _))]
  exact mul_le_mul_of_nonneg_left hact hk

lemma paperField_bounded {n : ℕ} (hn : 1 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1) (i : Fin 3)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O : ℝ} (hOp : OpB A O) :
    ∃ K : ℝ, ∀ v, |paperField wr g i A v| ≤ K := by
  refine ⟨(3 * (∑ j, ∑ k, A j k ^ 2)) * max 1 (((n : ℝ) * tA n / 2) * O ^ 2), ?_⟩
  intro v
  unfold paperField
  rw [abs_mul]
  apply mul_le_mul (paperPsi_bounded hn wr hc g i A v) _ (abs_nonneg _) (by positivity)
  unfold paperWeight
  split_ifs
  · exact (activationWeight_bounded hn wr g hs A hOp v).trans (le_max_right _ _)
  · simpa using le_max_left 1 (((n : ℝ) * tA n / 2) * O ^ 2)

noncomputable def paperNodeStatistic {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) : ℝ :=
  momN (stdGauss (Fin (n - 1))) 4 (paperField wr g i A)

lemma paperNodeStatistic_nonneg {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) : 0 ≤ paperNodeStatistic wr g i A :=
  BstLean.Part161.momN_nonneg _ _ _

/-- The real-valued statistic has exactly the order416 quantity used by the event. -/
theorem paperNodeStatistic_pow416 {n : ℕ} (hn : 1 ≤ n) (wr : WRet n)
    (hc : wr.2 ≠ 0) (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1) (i : Fin 3)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O : ℝ} (hOp : OpB A O) :
    ENNReal.ofReal (paperNodeStatistic wr g i A ^ 416) =
      latitudeStatistic416 (stdGauss (Fin (n - 1))) (paperField wr g i A) := by
  obtain ⟨K, hK⟩ := paperField_bounded hn wr hc g hs i A hOp
  have hm := (paperField_measurable wr g i).of_uncurry_left (x := A)
  have hi := mo_bdd_pow (μ := stdGauss (Fin (n - 1))) hm.abs
    (fun v => by simpa only [abs_abs] using hK v) 4
  rw [show (416 : ℕ) = 4 * 104 by rfl, pow_mul, paperNodeStatistic,
    BstLean.Part161.momN_pow _ (by norm_num : (4 : ℕ) ≠ 0),
    ENNReal.ofReal_pow (integral_nonneg fun _ => by positivity),
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => by positivity)]
  rfl

#print axioms statisticsTf_eq_paperPsi
#print axioms paperNodeStatistic_pow416

/-- The same event bounds the real order-four statistics, with no nodewise threshold. -/
theorem paperStatisticsEvent_real {n J : ℕ} (hn : 1 ≤ n) (wr : WRet n)
    (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O C : ℝ} (hOp : OpB A O)
    (hE : A ∈ paperStatisticsEvent wr ν node C) (i : Fin 3) :
    ∫⁻ g, ENNReal.ofReal (paperNodeStatistic wr (node g) i A ^ 416) ∂ν ≤
      ENNReal.ofReal (C ^ 416) := by
  simp_rw [paperNodeStatistic_pow416 hn wr hc _ (hs _) i A hOp]
  exact hE i

lemma paperNodeStatistic_mean {n : ℕ} (hn : 1 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1) (i : Fin 3)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O : ℝ} (hOp : OpB A O) :
    ∫ v, |paperField wr g i A v| ∂stdGauss (Fin (n - 1)) ≤
      paperNodeStatistic wr g i A := by
  obtain ⟨K, hK⟩ := paperField_bounded hn wr hc g hs i A hOp
  have hm := (paperField_measurable wr g i).of_uncurry_left (x := A)
  have h2 := mo_sq_int_le (μ := stdGauss (Fin (n - 1))) hm.abs
    (fun v => by simpa only [abs_abs] using hK v)
  have h4 := mo_sq_int_le (μ := stdGauss (Fin (n - 1))) (hm.abs.pow_const 2)
    (C := K ^ 2) (fun v => by
      rw [abs_pow, abs_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hK v) 2)
  have hp := pow_le_pow_left₀ (sq_nonneg _) h2 2
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
    (paperNodeStatistic_nonneg wr g i A)
  rw [paperNodeStatistic, BstLean.Part161.momN_pow _ (by norm_num : (4 : ℕ) ≠ 0)]
  convert hp.trans h4 using 1 <;> ring_nf

#print axioms paperStatisticsEvent_real
#print axioms paperNodeStatistic_mean
end BstLean.Part239
