import BstLean.Part223OriginalBias
import BstLean.Part223Kernel
import BstLean.Part223WeightedEnergy

/-! The energy and location fields use the same original Gaussian matrix. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170

variable {n : ℕ}

lemma scaledSecondLayer_distribution (n : ℕ) :
    Measure.map (fun M : Fin (mA n) → Fin (mA n) → ℝ => sqrt (tA n) • M)
      (Measure.pi fun _ : Fin (mA n) => stdGauss (Fin (mA n))) =
      gaussMat (mA n) (mA n) (tA n) := by
  have he := congrArg (Measure.map (matOf (tA n)))
    (BstLean.Part184.stdGauss_uncurry (mA n))
  have hu : Measurable (Function.uncurry : (Fin (mA n) → Fin (mA n) → ℝ) →
      (Fin (mA n) × Fin (mA n) → ℝ)) :=
    (MeasurableEquiv.curry _ _ ℝ).symm.measurable
  rw [Measure.map_map (measurable_matOf _) hu] at he
  exact he

noncomputable def originalEnergyFluct (c : Ret n) (g : ℕ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) : ℝ :=
  exWn (withA2 c M) g - originalEnergyBias c g M

lemma measurable_originalEnergyFluct (c : Ret n) (g : ℕ) :
    Measurable (originalEnergyFluct c g) :=
  (measurable_exWn_comp (measurable_withA2 c) measurable_const).sub
    (measurable_originalEnergyBias c g)

lemma originalPlaneMean_replace {m q : ℕ} (v : ℝ) (h g : Fin m → ℝ)
    (f : Matrix (Fin q) (Fin m) ℝ → ℝ) (M : Matrix (Fin q) (Fin m) ℝ) :
    originalPlaneMean v h g f M =
      ∫ N, f (replaceMatrix h g M N) ∂gaussMat q m v := by
  unfold originalPlaneMean planeMean
  exact integral_congr_ae (ae_of_all _ fun N =>
    congrArg f (plane_rebuild_eq_replace h g M N))

lemma originalPlaneMean_scaled (c : Ret n) (g : ℕ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :
    originalEnergyBias c g (sqrt (tA n) • M) =
      ∫ N, exWn (withA2 c (sqrt (tA n) •
        replaceMatrix (hB c) (a1Bar c (nodeS c g)) M N)) g
        ∂(Measure.pi fun _ : Fin (mA n) => stdGauss (Fin (mA n))) := by
  let f := fun N : Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
    exWn (withA2 c N) g
  have hf : Measurable f :=
    measurable_exWn_comp (measurable_withA2 c) measurable_const
  have hr : Measurable (fun N : Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      replaceMatrix (hB c) (a1Bar c (nodeS c g)) (sqrt (tA n) • M) N) := by
    apply Measurable.of_eval
    intro j
    exact (continuous_replaceTransverse (hB c) (a1Bar c (nodeS c g))).measurable.comp
      (measurable_const.prodMk (measurable_pi_apply j))
  change originalPlaneMean _ _ _ f _ = _
  rw [originalPlaneMean_replace, ← scaledSecondLayer_distribution n]
  erw [integral_map (measurable_const_smul (sqrt (tA n))).aemeasurable
    (hf.comp hr).aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun N => congrArg f (replaceMatrix_smul _ _ _ M N)

theorem originalEnergyFluct_scaled (hn : 1 ≤ n) (c : Ret n) (g : ℕ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :
    originalEnergyFluct c g (sqrt (tA n) • M) = originalNetworkEnergyFluct c g M := by
  have ht : 0 < tA n := by
    unfold tA mA
    positivity
  have hs : sqrt (tA n) ≠ 0 := (sqrt_pos.mpr ht).ne'
  unfold originalEnergyFluct originalNetworkEnergyFluct
  rw [originalPlaneMean_scaled]
  apply congrArg (fun b => exWn (withA2 c (sqrt (tA n) • M)) g - b)
  apply integral_congr_ae
  refine ae_of_all _ fun N => ?_
  have he : replaceMatrix (hB c)
      (vmean (stdGauss (Fin (n - 1))) (scaledLatitude c g)) M N =
      replaceMatrix (hB c) (a1Bar c (nodeS c g)) M N := by
    rw [scaledLatitude_mean]
    exact replaceMatrix_direction_smul (hB c) (a1Bar c (nodeS c g)) hs M N
  exact congrArg (fun P => exWn (withA2 c (sqrt (tA n) • P)) g) he.symm

theorem originalEnergyFluct_order18 (hn : 3 ≤ n) (c : Ret n) (g : ℕ)
    (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB (A1 c) O) :
    ∫⁻ M, ENNReal.ofReal (|originalEnergyFluct c g M| ^ 18)
      ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal ((BstLean.Part202.rowScale (stdGauss (Fin (n - 1)))
        (scaledLatitude c g) (sqrt (tA n *
          ((1 - nodeS c g ^ 2) * O ^ 2 / ((n : ℝ) - 2)))) * energyCoefficient18 n) ^ 18) := by
  rw [← scaledSecondLayer_distribution n]
  erw [lintegral_map ((measurable_originalEnergyFluct c g).abs.pow_const 18 |>.ennreal_ofReal)
      (measurable_const_smul (sqrt (tA n)))]
  simp_rw [originalEnergyFluct_scaled (by omega : 1 ≤ n)]
  exact originalNetworkEnergyFluct_order18 hn c g hs hO hOp

#print axioms scaledSecondLayer_distribution
#print axioms originalEnergyFluct_scaled
#print axioms originalEnergyFluct_order18
end BstLean.Part223
