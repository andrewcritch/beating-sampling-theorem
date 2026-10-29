import BstLean.Part222AgentLayer
import BstLean.Part222Integration

/-! The two-layer energy deviation is integrated over the actual Agent distribution. -/
namespace BstLean.Part222
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153
open BstLean.Part177 (TH)

lemma memLp32_of_moment {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : AEStronglyMeasurable f μ)
    (hi : Integrable (fun x => |f x|^32) μ) : MemLp f 32 μ := by
  apply (integrable_norm_rpow_iff hf (by norm_num : (32 : ℝ≥0∞) ≠ 0)
    (by norm_num : (32 : ℝ≥0∞) ≠ ∞)).1
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs] using hi

lemma norm32_of_moment {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : MemLp f 32 μ) {B : ℝ} (hB : 0 ≤ B)
    (hm : (∫ x, |f x|^32 ∂μ) ≤ B^32) : lpNorm f 32 μ ≤ B := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) hB
  rw [lpNorm_pow32 hf.aestronglyMeasurable]
  exact hm

noncomputable def energyDeviation {n : ℕ} (x : Fin n → ℝ) (a : TH n) : ℝ :=
  nrm (hid2 a.1 a.2 x)/√(n : ℝ)-1

lemma energyDeviation_continuous {n : ℕ} (x : Fin n → ℝ) :
    Continuous (energyDeviation x) := by
  unfold energyDeviation
  exact ((continuous_nrm.comp (BstLean.Part136.continuous_hid2_joint.comp
    (continuous_id.prodMk continuous_const))).div_const _).sub continuous_const

lemma secondDeviation_continuous {n : ℕ} (x : Fin n → ℝ) :
    Continuous (secondDeviation x) := by
  unfold secondDeviation
  exact (((continuous_nrm.comp (BstLean.Part136.continuous_hid2_joint.comp
    (continuous_id.prodMk continuous_const))).div_const _).sub
    ((firstRadius_continuous x).comp continuous_fst)).abs

noncomputable def energyWeightAllowance (n : ℕ) : ℝ :=
  2*agentLayerAllowance n+agentLayerAllowance n^2

lemma energyWeightAllowance_nonneg (n : ℕ) : 0 ≤ energyWeightAllowance n := by
  unfold energyWeightAllowance agentLayerAllowance
  have h := layerAllowance_nonneg (mA n)
  positivity

/-- No independent Agent weights are introduced at different inputs. -/
theorem energy_weight_moment {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ)
    (hx : normSq x = 1) :
    Integrable (fun a => |energyDeviation x a|^32) (nuA n) ∧
    (∫ a, |energyDeviation x a|^32 ∂nuA n) ≤ energyWeightAllowance n^32 := by
  let μ := gaussMat (mA n) n (2/(n : ℝ))
  let ν := gaussMat (mA n) (mA n) (2/(mA n : ℝ))
  let a := agentLayerAllowance n
  have ha : 0 ≤ a := layerAllowance_nonneg (mA n)
  let G := secondDeviation x
  let Q : TH n → ℝ := fun p => |firstRadius x p.1-1|
  have mG : Measurable G := (secondDeviation_continuous x).measurable
  have mQ : Measurable Q := ((firstRadius_continuous x).measurable.comp
    measurable_fst).sub_const 1 |>.abs
  have hG0 : ∀ p, 0 ≤ G p := fun p => abs_nonneg _
  have hQ0 : ∀ p, 0 ≤ Q p := fun p => abs_nonneg _
  have hR := firstRadius_moment hn x hx
  have hD := firstRadius_deviation hn x hx
  have hG : Integrable (fun p => G p^32) (nuA n) ∧
      (∫ p, G p^32 ∂nuA n) ≤ (a*(1+a))^32 := by
    obtain ⟨hi,hb⟩ := product_moment_bound μ ν (fun p => G p^32)
      (mG.pow_const _) (fun p => pow_nonneg (hG0 p) _)
      (fun A => (secondDeviation_moment hn x A).1)
      (fun A => a^32 * firstRadius x A^32) (hR.1.const_mul _)
      (fun A => mul_nonneg (pow_nonneg ha _) (pow_nonneg (firstRadius_nonneg _ _) _))
      (fun A => by
        have h := (secondDeviation_moment hn x A).2
        simpa only [a, agentLayerAllowance, G, mul_pow, mul_comm] using h)
    refine ⟨hi, hb.trans ?_⟩
    rw [integral_const_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left hR.2 (pow_nonneg ha _)
  have hQi : Integrable (fun p => Q p^32) (nuA n) := hD.1.comp_fst ν
  have hQm : (∫ p, Q p^32 ∂nuA n) ≤ a^32 := by
    change (∫ p, Q p^32 ∂μ.prod ν) ≤ _
    rw [integral_prod _ hQi]
    simpa [Q, ν] using hD.2
  have gmem : MemLp G 32 (nuA n) := memLp32_of_moment _ _ mG.aestronglyMeasurable
    (by simpa only [abs_of_nonneg (hG0 _)] using hG.1)
  have qmem : MemLp Q 32 (nuA n) := memLp32_of_moment _ _ mQ.aestronglyMeasurable
    (by simpa only [abs_of_nonneg (hQ0 _)] using hQi)
  have hgn : lpNorm G 32 (nuA n) ≤ a*(1+a) := norm32_of_moment _ _ gmem
    (by positivity) (by simpa only [abs_of_nonneg (hG0 _)] using hG.2)
  have hqn : lpNorm Q 32 (nuA n) ≤ a := norm32_of_moment _ _ qmem ha
    (by simpa only [abs_of_nonneg (hQ0 _)] using hQm)
  have hpt : ∀ p, ‖energyDeviation x p‖ ≤ (G+Q) p := by
    intro p
    change |nrm (hid2 p.1 p.2 x)/√(n : ℝ)-1| ≤
      |nrm (hid2 p.1 p.2 x)/√(n : ℝ)-firstRadius x p.1|+|firstRadius x p.1-1|
    exact abs_sub_le _ _ _
  have fmem : MemLp (energyDeviation x) 32 (nuA n) :=
    (gmem.add qmem).mono' (energyDeviation_continuous x).aestronglyMeasurable
      (Filter.Eventually.of_forall hpt)
  have hfn : lpNorm (energyDeviation x) 32 (nuA n) ≤ energyWeightAllowance n := by
    have ht := (lpNorm_mono_real (gmem.add qmem) hpt).trans
      ((lpNorm_add_le gmem (by norm_num)).trans (add_le_add hgn hqn))
    refine ht.trans_eq ?_
    unfold energyWeightAllowance
    change a*(1+a)+a = 2*a+a^2
    ring
  refine ⟨by simpa only [Real.norm_eq_abs] using fmem.integrable_norm_pow (by norm_num), ?_⟩
  have h := pow_le_pow_left₀ lpNorm_nonneg hfn 32
  rwa [lpNorm_pow32 fmem.aestronglyMeasurable] at h

#print axioms energy_weight_moment
end BstLean.Part222
