import BstLean.Part223NodeSupply
import BstLean.Part220RA

/-! The supplied scalar statistics feed the actual two RA16 moments. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (mkR tA biasF biasW)
open BstLean.Part161 (xLat)
open BstLean.Part53 (unitF53)
open BstLean.Part213 (radiusPolynomial)
open BstLean.Part220
open BstLean.Part186.RA (ρ2)

noncomputable def paperRAData {n : ℕ} (wr : WRet n) (g : ℕ)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (O Sm SM topF topW : ℝ) : RAData :=
  let s := nodeS (mkR wr (0, 0)) g
  let M := fun i => paperNodeStatistic wr g i A
  { Smin := Sm, Smax := SM
    D := paperPlaneBound n s (M 0) (M 1)
    H := paperPlaneBound n s (M 0) (M 1)
    V := paperVarianceBound n s (M 0) (M 1) (M 2)
    P := paperExceptionalBound n s O Sm (M 2)
    topF := topF, topW := topW }

lemma RAData_coefficients_nonneg {n : ℕ} (c : Ret n) (g : ℕ) {O : ℝ}
    (hO : 0 ≤ O) (d : RAData) (h : NodeStat c g d.Smin d.Smax d.D d.H d.V d.P) :
    0 ≤ d.f0 n O ∧ 0 ≤ d.f1 n O ∧ 0 ≤ d.f2 ∧
      0 ≤ d.w0 n O ∧ 0 ≤ d.w1 n O ∧ 0 ≤ d.w2 n O := by
  have hD := (DstN_nonneg c g).trans h.hD
  have hH := (hUN_nonneg c g).trans h.hH
  have hV := (V2N_nonneg c g).trans h.hV
  have hP := (piN_nonneg c g).trans h.hP
  have hS : 0 ≤ d.Smax := (le_max_left 0 _).trans h.hS2
  have ht := tA_nonneg n
  have hp0 := (BstLean.Part153.phiG_pos 0).le
  have hp1 := (BstLean.Part153.phiG_pos 1).le
  unfold RAData.f0 RAData.f1 RAData.f2 RAData.w0 RAData.w1 RAData.w2
    AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

/-- The row prices are scalar radius-polynomial inputs. NodeStat is supplied here. -/
theorem paperNode_RA16_supply {n : ℕ} (hn : 10 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O Sm SM topF topW : ℝ}
    (hO : 0 ≤ O) (hOp : OpB A O) (hSm : 0 < Sm)
    (hmin : Sm ≤ vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g))
    (hmax : vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) ≤ SM)
    (hgap : 0 < Sm / 2 - planeTraceCap n (nodeS (mkR wr (0, 0)) g) O)
    (hk : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ j, (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)) j ≠ 0)
    (hF : 0 ≤ topF) (hW : 0 ≤ topW)
    (hrowF : let d := paperRAData wr g A O Sm SM topF topW
      ∫ p, radiusPolynomial (d.f0 n O) (d.f1 n O) d.f2 p ^ 16 ∂ρ2 ≤ topF ^ 16)
    (hrowW : let d := paperRAData wr g A O Sm SM topF topW
      ∫ p, radiusPolynomial (d.w0 n O) (d.w1 n O) (d.w2 n O) p ^ 16 ∂ρ2 ≤ topW ^ 16) :
    let d := paperRAData wr g A O Sm SM topF topW
    (∫⁻ y, ENNReal.ofReal (|biasF (mkR wr (A, 0)) g
        (fun j => (y j).1) (fun j => (y j).2)| ^ 16)
      ∂(Measure.pi fun _ : Fin (mA n) => ρ2)) ≤ ENNReal.ofReal (d.locationBound n O) ∧
    (∫⁻ y, ENNReal.ofReal (|biasW (mkR wr (A, 0)) g
        (fun j => (y j).1) (fun j => (y j).2)| ^ 16)
      ∂(Measure.pi fun _ : Fin (mA n) => ρ2)) ≤ ENNReal.ofReal (d.energyBound n O) := by
  let d := paperRAData wr g A O Sm SM topF topW
  have hstat : NodeStat (mkR wr (A, 0)) g d.Smin d.Smax d.D d.H d.V d.P :=
    nodeStat_of_paperStatistics hn wr hc g hs A hO hOp hmin hmax hgap hk
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ :=
    RAData_coefficients_nonneg (mkR wr (A, 0)) g hO d hstat
  exact node_RA16_supply (by omega) (mkR wr (A, 0)) g hs hO hOp d
    ⟨hSm, hstat, hf0, hf1, hf2, hw0, hw1, hw2, hF, hW, hrowF, hrowW⟩

#print axioms RAData_coefficients_nonneg
#print axioms paperNode_RA16_supply

/-- The row moment is a finite sum of exact Gaussian radius moments. -/
noncomputable def radiusPolynomialMoment16 (a b c : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 17, ∑ j ∈ Finset.range (16 - i + 1),
    (a ^ i * ((16 : ℕ).choose i : ℝ) *
      (b ^ j * ((16 - i).choose j : ℝ) * c ^ (16 - i - j))) *
      ((1 / 2 : ℝ) ^ (-((j + 2 * (16 - i - j) : ℕ) + 2 : ℝ) / 2) *
        (1 / 2) * Gamma (((j + 2 * (16 - i - j) : ℕ) + 2 : ℝ) / 2))

lemma radiusPolynomialMoment16_eq (a b c : ℝ) :
    radiusPolynomialMoment16 a b c = ∫ p, radiusPolynomial a b c p ^ 16 ∂ρ2 :=
  (BstLean.Part213.radius_polynomial_power a b c 16).2.symm

noncomputable def radiusPolynomialRoot16 (a b c : ℝ) : ℝ :=
  radiusPolynomialMoment16 a b c ^ ((16 : ℝ)⁻¹)

lemma radiusPolynomialMoment16_nonneg (a b c : ℝ) :
    0 ≤ radiusPolynomialMoment16 a b c := by
  rw [radiusPolynomialMoment16_eq]
  exact integral_nonneg fun _ => by positivity

lemma radiusPolynomialRoot16_nonneg (a b c : ℝ) :
    0 ≤ radiusPolynomialRoot16 a b c :=
  Real.rpow_nonneg (radiusPolynomialMoment16_nonneg a b c) _

theorem radiusPolynomialRoot16_pow (a b c : ℝ) :
    radiusPolynomialRoot16 a b c ^ 16 = ∫ p, radiusPolynomial a b c p ^ 16 ∂ρ2 := by
  unfold radiusPolynomialRoot16
  exact (Real.rpow_inv_natCast_pow (radiusPolynomialMoment16_nonneg a b c)
    (by norm_num : (16 : ℕ) ≠ 0)).trans (radiusPolynomialMoment16_eq a b c)

/-- Both actual RA16 moments have supplied scalar statistics and supplied row moments. -/
theorem paperNode_RA16_exact {n : ℕ} (hn : 10 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O Sm SM : ℝ}
    (hO : 0 ≤ O) (hOp : OpB A O) (hSm : 0 < Sm)
    (hmin : Sm ≤ vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g))
    (hmax : vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) ≤ SM)
    (hgap : 0 < Sm / 2 - planeTraceCap n (nodeS (mkR wr (0, 0)) g) O)
    (hk : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ j, (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)) j ≠ 0) :
    let d0 := paperRAData wr g A O Sm SM 0 0
    let d := paperRAData wr g A O Sm SM
      (radiusPolynomialRoot16 (d0.f0 n O) (d0.f1 n O) d0.f2)
      (radiusPolynomialRoot16 (d0.w0 n O) (d0.w1 n O) (d0.w2 n O))
    (∫⁻ y, ENNReal.ofReal (|biasF (mkR wr (A, 0)) g
        (fun j => (y j).1) (fun j => (y j).2)| ^ 16)
      ∂(Measure.pi fun _ : Fin (mA n) => ρ2)) ≤ ENNReal.ofReal (d.locationBound n O) ∧
    (∫⁻ y, ENNReal.ofReal (|biasW (mkR wr (A, 0)) g
        (fun j => (y j).1) (fun j => (y j).2)| ^ 16)
      ∂(Measure.pi fun _ : Fin (mA n) => ρ2)) ≤ ENNReal.ofReal (d.energyBound n O) := by
  apply paperNode_RA16_supply hn wr hc g hs A hO hOp hSm hmin hmax hgap hk
    (radiusPolynomialRoot16_nonneg _ _ _) (radiusPolynomialRoot16_nonneg _ _ _)
  · exact (radiusPolynomialRoot16_pow _ _ _).symm.le
  · exact (radiusPolynomialRoot16_pow _ _ _).symm.le

#print axioms radiusPolynomialRoot16_pow
#print axioms paperNode_RA16_exact

noncomputable def exactPaperRAData {n : ℕ} (wr : WRet n) (g : ℕ)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (O Sm SM : ℝ) : RAData :=
  let d0 := paperRAData wr g A O Sm SM 0 0
  paperRAData wr g A O Sm SM
    (radiusPolynomialRoot16 (d0.f0 n O) (d0.f1 n O) d0.f2)
    (radiusPolynomialRoot16 (d0.w0 n O) (d0.w1 n O) (d0.w2 n O))

/-- The statistics and scalar row moments are conclusions, not moment premises. -/
theorem exactPaperNodeRASupply {n : ℕ} (hn : 10 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O Sm SM : ℝ}
    (hO : 0 ≤ O) (hOp : OpB A O) (hSm : 0 < Sm)
    (hmin : Sm ≤ vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g))
    (hmax : vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) ≤ SM)
    (hgap : 0 < Sm / 2 - planeTraceCap n (nodeS (mkR wr (0, 0)) g) O)
    (hk : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ j, (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)) j ≠ 0) :
    NodeRASupply (mkR wr (A, 0)) g O (exactPaperRAData wr g A O Sm SM) := by
  let d := exactPaperRAData wr g A O Sm SM
  have hstat : NodeStat (mkR wr (A, 0)) g d.Smin d.Smax d.D d.H d.V d.P :=
    nodeStat_of_paperStatistics hn wr hc g hs A hO hOp hmin hmax hgap hk
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ :=
    RAData_coefficients_nonneg (mkR wr (A, 0)) g hO d hstat
  exact ⟨hSm, hstat, hf0, hf1, hf2, hw0, hw1, hw2,
    radiusPolynomialRoot16_nonneg _ _ _, radiusPolynomialRoot16_nonneg _ _ _,
    (radiusPolynomialRoot16_pow _ _ _).symm.le,
    (radiusPolynomialRoot16_pow _ _ _).symm.le⟩

#print axioms exactPaperNodeRASupply
end BstLean.Part223
