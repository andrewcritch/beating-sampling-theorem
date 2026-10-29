import BstLean.Part223PlaneTransfer
import BstLean.Part223ScalarRA

/-! Location fluctuation and both bias supplies use the original second-layer matrix. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170
open BstLean.Part220
open BstLean.Part186.RA (ρ2)

variable {n : ℕ}

noncomputable def originalLocationBias (c : Ret n) (g : ℕ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) : ℝ :=
  originalPlaneMean (tA n) (hB c) (a1Bar c (nodeS c g))
    (fun N => exFn (withA2 c N) g) M

noncomputable def originalEnergyBias (c : Ret n) (g : ℕ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) : ℝ :=
  originalPlaneMean (tA n) (hB c) (a1Bar c (nodeS c g))
    (fun N => exWn (withA2 c N) g) M

noncomputable def originalLocationFluct (c : Ret n) (g : ℕ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) : ℝ :=
  exFn (withA2 c M) g - originalLocationBias c g M

lemma measurable_originalLocationBias (c : Ret n) (g : ℕ) :
    Measurable (originalLocationBias c g) :=
  measurable_originalPlaneMean _ _ _
    (measurable_exFn_comp (measurable_withA2 c) measurable_const)

lemma measurable_originalEnergyBias (c : Ret n) (g : ℕ) :
    Measurable (originalEnergyBias c g) :=
  measurable_originalPlaneMean _ _ _
    (measurable_exWn_comp (measurable_withA2 c) measurable_const)

lemma measurable_originalLocationFluct (c : Ret n) (g : ℕ) :
    Measurable (originalLocationFluct c g) :=
  (measurable_exFn_comp (measurable_withA2 c) measurable_const).sub
    (measurable_originalLocationBias c g)

theorem originalLocationFluct_order24 (hn : 3 ≤ n) (c : Ret n) (g : ℕ)
    (hs : nodeS c g ^ 2 ≤ 1) {O q : ℝ} (hO : 0 ≤ O) (hOp : OpB (A1 c) O)
    (hq0 : 0 ≤ q) (hq : 1 - nodeS c g ^ 2 ≤ q) :
    (∫⁻ M, ENNReal.ofReal (|originalLocationFluct c g M| ^ 24)
      ∂gaussMat (mA n) (mA n) (tA n)) ≤
    ENNReal.ofReal (2 * (sqrt (n : ℝ) *
      sqrt (tA n * (q * O ^ 2 / ((n : ℝ) - 2))) / 2) ^ 24 *
        (2 ^ 12 * ((12 : ℕ).factorial : ℝ))) := by
  unfold originalLocationFluct originalLocationBias
  rw [originalPlaneFluct_moment _ _ _
    (measurable_exFn_comp (measurable_withA2 c) measurable_const)]
  exact BstLean.Part216.network_location24_planes hn c g hs hO hOp hq0 hq

lemma originalLocationBias_moment (c : Ret n) (g k : ℕ) :
    (∫⁻ M, ENNReal.ofReal (|originalLocationBias c g M| ^ k)
      ∂gaussMat (mA n) (mA n) (tA n)) =
    ∫⁻ y, ENNReal.ofReal (|biasF c g (fun j => (y j).1) (fun j => (y j).2)| ^ k)
      ∂(Measure.pi fun _ : Fin (mA n) => ρ2) := by
  unfold originalLocationBias
  rw [originalPlaneMean_moment _ _ _
    (measurable_exFn_comp (measurable_withA2 c) measurable_const)]
  change (∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (|biasF c g ξ₁ ξ₂| ^ k)
    ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))) = _
  refine BstLean.Part186.RA.lint_transfer
    (fun y => ENNReal.ofReal (|biasF c g (fun j => (y j).1) (fun j => (y j).2)| ^ k)) ?_
  have hm : Measurable (fun p : (Fin (mA n) → ℝ × ℝ) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      exFn (withA2 c (Mpl (hB c) (BstLean.Part134.res (hB c) (a1Bar c (nodeS c g)))
        (cOf (tA n) (hB c) (fun j => (p.1 j).1))
        (cOf (tA n) (BstLean.Part134.res (hB c) (a1Bar c (nodeS c g)))
          (fun j => (p.1 j).2)) p.2)) g) := by
    apply measurable_exFn_comp _ measurable_const
    apply (measurable_withA2 c).comp
    exact measurable_reb_comp measurable_const
      (measurable_cOf_comp _ measurable_const (by fun_prop))
      (measurable_reb_comp measurable_const
        (measurable_cOf_comp _ measurable_const (by fun_prop)) measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right'.measurable).abs.pow_const k
    |>.ennreal_ofReal

lemma originalEnergyBias_moment (c : Ret n) (g k : ℕ) :
    (∫⁻ M, ENNReal.ofReal (|originalEnergyBias c g M| ^ k)
      ∂gaussMat (mA n) (mA n) (tA n)) =
    ∫⁻ y, ENNReal.ofReal (|biasW c g (fun j => (y j).1) (fun j => (y j).2)| ^ k)
      ∂(Measure.pi fun _ : Fin (mA n) => ρ2) := by
  unfold originalEnergyBias
  rw [originalPlaneMean_moment _ _ _
    (measurable_exWn_comp (measurable_withA2 c) measurable_const)]
  change (∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (|biasW c g ξ₁ ξ₂| ^ k)
    ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))) = _
  refine BstLean.Part186.RA.lint_transfer
    (fun y => ENNReal.ofReal (|biasW c g (fun j => (y j).1) (fun j => (y j).2)| ^ k)) ?_
  have hm : Measurable (fun p : (Fin (mA n) → ℝ × ℝ) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      exWn (withA2 c (Mpl (hB c) (BstLean.Part134.res (hB c) (a1Bar c (nodeS c g)))
        (cOf (tA n) (hB c) (fun j => (p.1 j).1))
        (cOf (tA n) (BstLean.Part134.res (hB c) (a1Bar c (nodeS c g)))
          (fun j => (p.1 j).2)) p.2)) g) := by
    apply measurable_exWn_comp _ measurable_const
    apply (measurable_withA2 c).comp
    exact measurable_reb_comp measurable_const
      (measurable_cOf_comp _ measurable_const (by fun_prop))
      (measurable_reb_comp measurable_const
        (measurable_cOf_comp _ measurable_const (by fun_prop)) measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right'.measurable).abs.pow_const k
    |>.ennreal_ofReal

theorem originalBias_RA16_supply (hn : 2 ≤ n) (c : Ret n) (g : ℕ)
    (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB (A1 c) O)
    (d : RAData) (h : NodeRASupply c g O d) :
    (∫⁻ M, ENNReal.ofReal (|originalLocationBias c g M| ^ 16)
      ∂gaussMat (mA n) (mA n) (tA n)) ≤ ENNReal.ofReal (d.locationBound n O) ∧
    (∫⁻ M, ENNReal.ofReal (|originalEnergyBias c g M| ^ 16)
      ∂gaussMat (mA n) (mA n) (tA n)) ≤ ENNReal.ofReal (d.energyBound n O) := by
  rw [originalLocationBias_moment, originalEnergyBias_moment]
  exact node_RA16_supply (by omega) c g hs hO hOp d h

#print axioms originalLocationFluct_order24
#print axioms originalLocationBias_moment
#print axioms originalEnergyBias_moment
#print axioms originalBias_RA16_supply
end BstLean.Part223
