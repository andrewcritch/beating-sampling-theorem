import BstLean.Part239Frame
import BstLean.Part239Activation
import BstLean.Part239Mixed

/-! The paper's third field includes its first-layer activation weight. -/
namespace BstLean.Part239
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part172
open BstLean.Part170 (mkR tA)
open BstLean.Part171 (tA_nonneg)
open BstLean.Part161 (uHat xLat)
open BstLean.Part162 (dirW)
open BstLean.Part53 (unitF53)
open BstLean.Part167 (latSq D1A1)
open BstLean.Part220

noncomputable def paperDirection {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (v : Fin (n - 1) → ℝ) : Fin (mA n) → ℝ :=
  (sqrt (tA n))⁻¹ • statisticsField wr g i A v

lemma paperDirection_bound {n : ℕ} (hn : 1 ≤ n) (wr : WRet n) (g : ℕ) (i : Fin 3)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (v : Fin (n - 1) → ℝ) :
    normSq (paperDirection wr g i A v) ≤ 1 := by
  have ht : 0 < tA n := by
    unfold tA mA
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  rw [paperDirection, normSq_smul, inv_pow, sq_sqrt ht.le]
  calc
    (tA n)⁻¹ * normSq (statisticsField wr g i A v) ≤ (tA n)⁻¹ * tA n :=
      mul_le_mul_of_nonneg_left (statisticsField_bound wr g i A v) (inv_nonneg.mpr ht.le)
    _ = 1 := inv_mul_cancel₀ ht.ne'

noncomputable def paperPsi {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (v : Fin (n - 1) → ℝ) : ℝ :=
  latSq (vecMul (paperDirection wr g i A v)
    (D1A1 A (xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v))))
    (uHat (mkR wr (0, 0))) (dirW (mkR wr (0, 0)) (unitF53 v))

noncomputable def activationWeight {n : ℕ} (wr : WRet n) (g : ℕ)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (v : Fin (n - 1) → ℝ) : ℝ :=
  ((n : ℝ) * tA n / 2) * normSq
    (reluV (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)))

noncomputable def activationBound (n : ℕ) : ℝ :=
  ((n : ℝ) * tA n / 2) *
    ((2 / (n : ℝ)) * (sqrt ((mA n : ℝ) / 2) + BstLean.Part152.gaussMomConst 832) ^ 2)

noncomputable def paperWeight {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (v : Fin (n - 1) → ℝ) : ℝ :=
  if i = 2 then activationWeight wr g A v else 1

noncomputable def paperField {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (v : Fin (n - 1) → ℝ) : ℝ :=
  paperPsi wr g i A v * paperWeight wr g i A v

lemma paperPsi_moment832 {n q : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (wr : WRet n) (hc : wr.2 ≠ 0) (g : ℕ)
    (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1) (i : Fin 3)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    ∫⁻ A, ENNReal.ofReal (|paperPsi wr g i A v| ^ 832)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ ENNReal.ofReal (frameConstant1664 n q 1 ^ 832) := by
  simp_rw [Even.pow_abs (by decide : Even 832)]
  rw [frameConstant1664_pow hn hq]
  apply frame_mom1664 hn hq hc hs hv
  · intro A A' hx hu hr
    exact congrArg (fun z => (sqrt (tA n))⁻¹ • z)
      (statisticsField_admissible (by omega) wr hc g i v A A' hx hu hr)
  · norm_num
  · exact fun A => paperDirection_bound (by omega) wr g i A v

lemma activationWeight_moment832 {n : ℕ} (hn : 1 ≤ n) (wr : WRet n) (g : ℕ)
    (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1) (v : Fin (n - 1) → ℝ) :
    ∫⁻ A, ENNReal.ofReal (|activationWeight wr g A v| ^ 832)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ ENNReal.ofReal (activationBound n ^ 832) := by
  have hk : 0 ≤ (n : ℝ) * tA n / 2 := by
    have := tA_nonneg n
    positivity
  simp_rw [Even.pow_abs (by decide : Even 832), activationWeight, mul_pow,
    ENNReal.ofReal_mul (pow_nonneg hk 832)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl (activation_moment1664
    (normSq_xLat_le' hn _ hs v) (by positivity : (0 : ℝ) ≤ 2 / (n : ℝ)))).trans_eq ?_
  rw [← ENNReal.ofReal_mul (pow_nonneg hk 832), ← mul_pow]
  rfl

lemma measurable_unscaled_Tf {n : ℕ} (c₀ : Ret n) (s : ℝ)
    {F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ}
    (hF : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2)) :
    Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => latSq (vecMul (F p.1 p.2) (D1A1 p.1 (xLat c₀ s (unitF53 p.2)))) (uHat c₀) (dirW c₀ (unitF53 p.2))) := by
  have hx : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      xLat c₀ s (unitF53 p.2)) :=
    BstLean.Part161.measurable_xLat_comp c₀ measurable_const
      (BstLean.Part53.measurable_unitF.comp measurable_snd)
  have hD := mk_meas_D1A1 measurable_fst hx
  have hV : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      vecMul (F p.1 p.2) (D1A1 p.1 (xLat c₀ s (unitF53 p.2)))) := by
    exact (mk_cont_vecMul (n := n)).measurable.comp (hF.prodMk hD)
  have hW : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      dirW c₀ (unitF53 p.2)) := by
    unfold dirW
    have hc : Continuous (fun e : Fin (n - 1) → ℝ =>
        (BstLean.Part161.hhMat (uHat c₀)).mulVec (BstLean.Part161.consV (n := n) 0 e)) := by
      have := BstLean.Part162.continuous_consV (n := n)
      exact Continuous.matrix_mulVec continuous_const
        (this.comp (continuous_const.prodMk continuous_id))
    exact hc.measurable.comp (BstLean.Part53.measurable_unitF.comp measurable_snd)
  have hL := mk_cont_latSq (n := n) (uHat c₀)
  have hLW : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      latSq (vecMul (F p.1 p.2) (D1A1 p.1 (xLat c₀ s (unitF53 p.2)))) (uHat c₀)
        (dirW c₀ (unitF53 p.2))) :=
    hL.measurable.comp (f := fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      (vecMul (F p.1 p.2) (D1A1 p.1 (xLat c₀ s (unitF53 p.2))), dirW c₀ (unitF53 p.2)))
      (hV.prodMk hW)
  exact hLW


lemma paperPsi_measurable {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3) :
    Measurable (Function.uncurry (paperPsi wr g i)) :=
  measurable_unscaled_Tf _ _
    ((statisticsField_measurable wr g i).const_smul ((sqrt (tA n))⁻¹))

lemma activationWeight_measurable {n : ℕ} (wr : WRet n) (g : ℕ) :
    Measurable (Function.uncurry (activationWeight wr g)) := by
  have hx : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 p.2)) :=
    BstLean.Part161.measurable_xLat_comp _ measurable_const
      (BstLean.Part53.measurable_unitF.comp measurable_snd)
  exact (measurable_normSq.comp (gd_relu_cont.measurable.comp
    (measurable_fst.prodMk hx))).const_mul _

lemma paperField_measurable {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3) :
    Measurable (Function.uncurry (paperField wr g i)) := by
  unfold paperField paperWeight
  split_ifs
  · exact (paperPsi_measurable wr g i).mul (activationWeight_measurable wr g)
  · exact (paperPsi_measurable wr g i).mul measurable_const

noncomputable def paperStatisticsBound (n q : ℕ) : ℝ :=
  frameConstant1664 n q 1 * max 1 (activationBound n)

lemma paperStatisticsBound_nonneg (n q : ℕ) : 0 ≤ paperStatisticsBound n q :=
  mul_nonneg (frameConstant1664_nonneg (by norm_num))
    (le_trans (by norm_num) (le_max_left _ _))

lemma paperStatisticsBound_pos {n q : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q) :
    0 < paperStatisticsBound n q := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmR : (0 : ℝ) < mA n := by
    exact_mod_cast (show 0 < mA n by unfold mA; positivity)
  have hdR : (2 : ℝ) ≤ (n - 1 - 1 : ℕ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hR : 0 < BstLean.Part212.exactRadius (n - 1 - 1) 832 := by
    unfold BstLean.Part212.exactRadius
    exact div_pos (Real.rpow_pos_of_pos (BstLean.Part212.radialProduct_pos (by omega) _) _)
      (sqrt_pos.mpr (by linarith))
  have hmax : 0 < max 1 (activationBound n) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  unfold paperStatisticsBound frameConstant1664
  positivity

lemma paperWeight_measurable {n : ℕ} (wr : WRet n) (g : ℕ) (i : Fin 3)
    (v : Fin (n - 1) → ℝ) :
    Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => paperWeight wr g i A v) := by
  unfold paperWeight
  split_ifs
  · exact (activationWeight_measurable wr g).of_uncurry_right
  · exact measurable_const

lemma paperWeight_moment832 {n : ℕ} (hn : 1 ≤ n) (wr : WRet n) (g : ℕ)
    (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1) (i : Fin 3) (v : Fin (n - 1) → ℝ) :
    ∫⁻ A, ENNReal.ofReal (|paperWeight wr g i A v| ^ 832)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ ENNReal.ofReal (max 1 (activationBound n) ^ 832) := by
  unfold paperWeight
  split_ifs
  · refine (activationWeight_moment832 hn wr g hs v).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ _ (le_max_right _ _) 832
    unfold activationBound
    have := tA_nonneg n
    positivity
  · simp only [abs_one, one_pow, ENNReal.ofReal_one, lintegral_one, measure_univ]
    simpa only [one_pow, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
        (le_max_left 1 (activationBound n)) 832)

/-- The weighted third field uses Holder on the same first-layer matrix. -/
theorem paperField_moment416 {n q : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (wr : WRet n) (hc : wr.2 ≠ 0) (g : ℕ)
    (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1) (i : Fin 3)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    ∫⁻ A, ENNReal.ofReal (|paperField wr g i A v| ^ 416)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ ENNReal.ofReal (paperStatisticsBound n q ^ 416) := by
  unfold paperField paperStatisticsBound
  exact product_moment416 _
    (f := fun A => paperPsi wr g i A v) (g := fun A => paperWeight wr g i A v)
    (A := frameConstant1664 n q 1) (B := max 1 (activationBound n))
    (paperPsi_measurable wr g i).of_uncurry_right
    (paperWeight_measurable wr g i v) (frameConstant1664_nonneg (by norm_num))
    (le_trans (by norm_num) (le_max_left _ _))
    (paperPsi_moment832 hn hq wr hc g hs i hv)
    (paperWeight_moment832 (by omega) wr g hs i v)

/-- The paper order-four latitude statistic has the required order416 first-layer moment. -/
theorem paperLatitude_moment416 {n q : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (wr : WRet n) (hc : wr.2 ≠ 0) (g : ℕ)
    (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1) (i : Fin 3) :
    ∫⁻ A, latitudeStatistic416 (stdGauss (Fin (n - 1))) (paperField wr g i A)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ ENNReal.ofReal (paperStatisticsBound n q ^ 416) := by
  apply latitudeStatistic416_moment _ _ (paperField_measurable wr g i)
  have hz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have h0 := BstLean.Part168.stdGauss_zero (by omega : 1 ≤ n - 1)
    rw [ae_iff]
    simpa using h0
  filter_upwards [hz] with v hv
  exact paperField_moment416 hn hq wr hc g hs i hv

#print axioms paperPsi_moment832
#print axioms activationWeight_moment832
#print axioms paperField_moment416
#print axioms paperLatitude_moment416
end BstLean.Part239
