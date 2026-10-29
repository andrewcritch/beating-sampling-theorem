import BstLean.Part292LatitudeData
import BstLean.Part239NodeSupply

/-! The latitude-factored data are the scalar statistics of the original first matrix. -/
namespace BstLean.Part292
open MeasureTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170 BstLean.Part171
open BstLean.Part220 BstLean.Part223

noncomputable def basePlane (n : ℕ) (M0 M1 : ℝ) : ℝ :=
  tA n / ((n : ℝ)-2)*(M0+M1)

noncomputable def baseVariance (n : ℕ) (M2 : ℝ) : ℝ :=
  (8*tA n/(n : ℝ))/((n : ℝ)-2)*M2

noncomputable def baseGap (n : ℕ) (O σ : ℝ) : ℝ :=
  σ^2/2-2*tA n*O^2/((n : ℝ)-2)

noncomputable def baseExceptionalCoefficient (n : ℕ) (O σ : ℝ) : ℝ :=
  BstLean.Part162.cLS 4 ^ 8 * (8*tA n/(n : ℝ))^4 * inverseRadius8 (n-1) /
    baseGap n O σ ^ 8

theorem paperPlane_factor (n : ℕ) (s M0 M1 : ℝ) :
    paperPlaneBound n s M0 M1 = (1-s^2)*basePlane n M0 M1 := by
  unfold paperPlaneBound basePlane
  ring

theorem paperVariance_factor (n : ℕ) (s M0 M1 M2 : ℝ) :
    paperVarianceBound n s M0 M1 M2 =
      (1-s^2)*baseVariance n M2+((1-s^2)*basePlane n M0 M1)^2 := by
  unfold paperVarianceBound energyGradientCoefficient baseVariance
  rw [paperPlane_factor]
  ring

theorem paperExceptional_factor (n : ℕ) {s : ℝ} (hs : 0 < 1-s^2)
    (O σ M2 : ℝ) :
    paperExceptionalBound n s O ((1-s^2)*σ^2) M2 =
      (baseExceptionalCoefficient n O σ*M2^4)/(1-s^2)^4 := by
  have hden : (1-s^2)*σ^2/2-planeTraceCap n s O = (1-s^2)*baseGap n O σ := by
    unfold planeTraceCap baseGap
    ring
  by_cases hg : baseGap n O σ = 0
  · simp [paperExceptionalBound, hden, baseExceptionalCoefficient, hg]
  unfold paperExceptionalBound
  rw [hden]
  unfold energyEighthBound energyGradientCoefficient baseExceptionalCoefficient
  have he : 8*tA n/(n : ℝ)*(1-s^2)*M2 = (1-s^2)*(8*tA n/(n : ℝ)*M2) := by ring
  rw [he]
  simp only [mul_pow, div_pow]
  field_simp [hs.ne', hg] <;> ring

theorem latitudeNodeStat {n : ℕ} (hn : 10 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O σ sp : ℝ}
    (hO : 0 ≤ O) (hOp : OpB A O)
    (hq : 0 < 1-nodeS (mkR wr (0,0)) g ^2)
    (hmin : (1-nodeS (mkR wr (0,0)) g ^2)*σ^2 ≤
      vsig2 (mkR wr (A,0)) (nodeS (mkR wr (A,0)) g))
    (hmax : vsig2 (mkR wr (A,0)) (nodeS (mkR wr (A,0)) g) ≤ sp^2)
    (hgap : 0 < baseGap n O σ)
    (hk : ∀ᵐ v ∂BstLean.Part29.stdGauss (Fin (n-1)), ∀ j,
      (A *ᵥ BstLean.Part161.xLat (mkR wr (0,0)) (nodeS (mkR wr (0,0)) g)
        (BstLean.Part53.unitF53 v)) j ≠ 0) :
    let M := fun i => paperNodeStatistic wr g i A
    let d := latitudeRAData (1-nodeS (mkR wr (0,0)) g^2) σ sp
      (basePlane n (M 0) (M 1)) (baseVariance n (M 2))
      (baseExceptionalCoefficient n O σ*(M 2)^4)
    NodeStat (mkR wr (A,0)) g d.Smin d.Smax d.D d.H d.V d.P := by
  have hden : (1-nodeS (mkR wr (0,0)) g^2)*σ^2/2-
      planeTraceCap n (nodeS (mkR wr (0,0)) g) O =
      (1-nodeS (mkR wr (0,0)) g^2)*baseGap n O σ := by
    unfold planeTraceCap baseGap
    ring
  have h := nodeStat_of_paperStatistics hn wr hc g (by linarith) A hO hOp hmin hmax
    (by rw [hden]; exact mul_pos hq hgap) hk
  dsimp only at h ⊢
  simp only [latitudeRAData, paperPlane_factor, paperVariance_factor,
    paperExceptional_factor n hq] at h ⊢
  exact h

theorem base_statistics_moments {n J : ℕ} (hn : 10 ≤ n) (wr : WRet n)
    (ν : Measure (Fin J)) (node : Fin J → ℕ)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {C O σ : ℝ}
    (hE : A ∈ BstLean.Part239.node416Event wr ν node C) :
    MomentBound ν 416
      (fun g => basePlane n (paperNodeStatistic wr (node g) 0 A)
        (paperNodeStatistic wr (node g) 1 A)) (tA n/((n : ℝ)-2)*(C+C)) ∧
    MomentBound ν 416
      (fun g => baseVariance n (paperNodeStatistic wr (node g) 2 A))
      ((8*tA n/n)/((n : ℝ)-2)*C) ∧
    MomentBound ν 104
      (fun g => baseExceptionalCoefficient n O σ*(paperNodeStatistic wr (node g) 2 A)^4)
      (baseExceptionalCoefficient n O σ*C^4) := by
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ)-2 := by linarith
  have ht := tA_nonneg n
  have hr := (inverseRadius8_pos (by omega : 8 < n-1)).le
  exact ⟨((hE 0).add (by norm_num) (hE 1)).scale (by positivity),
    (hE 2).scale (by positivity),
    ((hE 2).power (k := 104) (r := 4)).scale
      (by unfold baseExceptionalCoefficient; positivity)⟩

end BstLean.Part292
