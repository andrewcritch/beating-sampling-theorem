import BstLean.Part223ScalarStatistics
import BstLean.Part173Cov

/-! The scalar statistics supply the installed node-statistics record. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part172 (e1v_normSq_le e2v_normSq_le)
open BstLean.Part170 (mkR tA aLat vmean vmean_aLat)
open BstLean.Part161 (xLat)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

noncomputable def planeTraceCap (n : ℕ) (s O : ℝ) : ℝ :=
  2 * tA n * ((1 - s ^ 2) * O ^ 2 / ((n : ℝ) - 2))

/-- The covariance cap holds at each node without a statistics event. -/
theorem DstN_le_planeTraceCap (hn : 3 ≤ n) (c : Ret n) (g : ℕ)
    (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB (A1 c) O) :
    DstN c g ≤ planeTraceCap n (nodeS c g) O := by
  let s := nodeS c g
  have hK := BstLean.Part170.aLat_bdd (by omega : 1 ≤ n) c hs hO hOp
  have hi : ∀ e : Fin (mA n) → ℝ,
      Integrable (fun v => (e ⬝ᵥ (aLat c s v - a1Bar c s)) ^ 2)
        (stdGauss (Fin (n - 1))) := by
    intro e
    exact BstLean.Part170.int_comp_bdd (BstLean.Part170.measurable_aLat c s) hK
      ((continuous_const.dotProduct (continuous_id.sub continuous_const)).pow 2)
  have he : DstN c g =
      (∫ v, (e1v c ⬝ᵥ (aLat c s v - a1Bar c s)) ^ 2 ∂stdGauss (Fin (n - 1))) +
      (∫ v, (e2v c g ⬝ᵥ (aLat c s v - a1Bar c s)) ^ 2 ∂stdGauss (Fin (n - 1))) := by
    unfold DstN
    simp_rw [q1_eq_dot, q2_eq_dot]
    exact integral_add (hi _) (hi _)
  have h1 := BstLean.Part173.cov_bound_lat hn c hs hO hOp (e1v c)
  have h2 := BstLean.Part173.cov_bound_lat hn c hs hO hOp (e2v c g)
  simp only [vmean_aLat] at h1 h2
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hB : 0 ≤ (1 - s ^ 2) * O ^ 2 / ((n : ℝ) - 2) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg O)) (by linarith)
  have h1' := h1.trans (mul_le_mul_of_nonneg_left (e1v_normSq_le c) hB)
  have h2' := h2.trans (mul_le_mul_of_nonneg_left (e2v_normSq_le c g) hB)
  rw [he]
  calc
    _ ≤ ((1 - s ^ 2) * O ^ 2 / ((n : ℝ) - 2)) * tA n +
        ((1 - s ^ 2) * O ^ 2 / ((n : ℝ) - 2)) * tA n := add_le_add h1' h2'
    _ = planeTraceCap n (nodeS c g) O := by unfold planeTraceCap; dsimp [s]; ring

noncomputable def paperPlaneBound (n : ℕ) (s M1 M2 : ℝ) : ℝ :=
  (1 - s ^ 2) * tA n * (M1 + M2) / ((n : ℝ) - 2)

noncomputable def paperVarianceBound (n : ℕ) (s M1 M2 M3 : ℝ) : ℝ :=
  energyGradientCoefficient n s * M3 / ((n : ℝ) - 2) + paperPlaneBound n s M1 M2 ^ 2

noncomputable def paperExceptionalBound (n : ℕ) (s O Smin M3 : ℝ) : ℝ :=
  energyEighthBound n s M3 / (Smin / 2 - planeTraceCap n s O) ^ 8

/-- All scalar node statistics follow from the actual first-layer fields.
The eighth-moment factor is the exact inverse radial product. -/
theorem nodeStat_of_paperStatistics (hn : 10 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O Sm SM : ℝ}
    (hO : 0 ≤ O) (hOp : OpB A O)
    (hmin : Sm ≤ vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g))
    (hmax : vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) ≤ SM)
    (hgap : 0 < Sm / 2 - planeTraceCap n (nodeS (mkR wr (0, 0)) g) O)
    (hk : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ j, (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)) j ≠ 0) :
    let s := nodeS (mkR wr (0, 0)) g
    let M := fun i => paperNodeStatistic wr g i A
    NodeStat (mkR wr (A, 0)) g Sm SM (paperPlaneBound n s (M 0) (M 1))
      (paperPlaneBound n s (M 0) (M 1)) (paperVarianceBound n s (M 0) (M 1) (M 2))
      (paperExceptionalBound n s O Sm (M 2)) := by
  dsimp only
  let c := mkR wr (A, 0)
  have hrad := (inverseRadius8_pos (by omega : 8 < n - 1)).le
  have hD := DstN_le_paperStatistics (by omega) wr hc g hs A hO hOp hk
  have hH := hUN_le_paperStatistics (by omega) wr hc g hs A hO hOp hk
  have hV := energyVariance_le_paperStatistic (by omega) wr hc g hs A hO hOp hk
  have h8 := energyEighth_le_paperStatistic hn wr hc g hs A hO hOp hk
  have hcap := DstN_le_planeTraceCap (by omega) c g hs hO hOp
  change Sm ≤ vsig2 c (nodeS c g) at hmin
  change 0 < Sm / 2 - planeTraceCap n (nodeS c g) O at hgap
  have hgap' : 0 < vsig2 c (nodeS c g) / 2 - DstN c g := by
    linarith only [hmin, hcap, hgap]
  have hP := piN_le (by omega) c g hs hO hOp (by linarith)
  refine ⟨hmin, hmax, hD, hH, ?_, ?_⟩
  · rw [V2N_eq (by omega) (mkR wr (A, 0)) g hs hO hOp]
    exact add_le_add hV (pow_le_pow_left₀ (DstN_nonneg c g) hD 2)
  · refine hP.trans ?_
    unfold paperExceptionalBound
    apply div_le_div₀
    · unfold energyEighthBound
      positivity
    · exact h8
    · positivity
    · apply pow_le_pow_left₀ hgap.le
      change Sm / 2 - planeTraceCap n (nodeS c g) O ≤
        vsig2 c (nodeS c g) / 2 - DstN c g
      linarith

#print axioms DstN_le_planeTraceCap
#print axioms nodeStat_of_paperStatistics

/-- One null set handles every node. This adds no positive event charge. -/
theorem paperNodes_kink_ae {J : ℕ} (hn : 2 ≤ n) (wr : WRet n) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1) :
    ∀ᵐ A ∂gaussMat (mA n) n (2 / (n : ℝ)), ∀ g,
      ∀ᵐ v ∂stdGauss (Fin (n - 1)),
        ∀ j, (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) (node g)) (unitF53 v)) j ≠ 0 := by
  rw [ae_all_iff]
  intro g
  exact BstLean.Part172.kink_ae hn (mkR wr (0, 0)) (hs g)

/-- Almost every first-layer matrix satisfies the scalar transfer at every fixed node. -/
theorem nodeStat_of_paperStatistics_ae {J : ℕ} (hn : 10 ≤ n) (wr : WRet n)
    (hc : wr.2 ≠ 0) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O)
    (Sm SM : Fin J → ℝ)
    (hgap : ∀ g, 0 < Sm g / 2 - planeTraceCap n (nodeS (mkR wr (0, 0)) (node g)) O) :
    ∀ᵐ A ∂gaussMat (mA n) n (2 / (n : ℝ)), OpB A O → ∀ g,
      Sm g ≤ vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) (node g)) →
      vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) (node g)) ≤ SM g →
      let s := nodeS (mkR wr (0, 0)) (node g)
      let M := fun i => paperNodeStatistic wr (node g) i A
      NodeStat (mkR wr (A, 0)) (node g) (Sm g) (SM g)
        (paperPlaneBound n s (M 0) (M 1)) (paperPlaneBound n s (M 0) (M 1))
        (paperVarianceBound n s (M 0) (M 1) (M 2))
        (paperExceptionalBound n s O (Sm g) (M 2)) := by
  filter_upwards [paperNodes_kink_ae (by omega) wr node hs] with A hA
  intro hOp g hmin hmax
  exact nodeStat_of_paperStatistics hn wr hc (node g) (hs g) A hO hOp hmin hmax
    (hgap g) (hA g)

#print axioms paperNodes_kink_ae
#print axioms nodeStat_of_paperStatistics_ae
end BstLean.Part223
