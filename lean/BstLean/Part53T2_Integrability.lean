import BstLean.Part53T2_Comparison
import BstLean.Part43Upper

namespace BstLean.Part53.T2Aux

open MeasureTheory
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Tens uJ contr varU sdU)
open BstLean.Part40 (SphLaw)
variable {n d : ℕ}

private def AllLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : Prop := ∀ p : ℝ≥0, MemLp f p μ

private lemma allLp_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : AllLp μ f) (hg : AllLp μ g) :
    AllLp μ (fun x => f x * g x) := by
  intro p
  letI : ENNReal.HolderTriple ((2 * p : ℝ≥0) : ℝ≥0∞)
      ((2 * p : ℝ≥0) : ℝ≥0∞) (p : ℝ≥0∞) := by
    constructor
    simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]
    rw [ENNReal.mul_inv (by left; norm_num) (by left; norm_num)]
    rw [← add_mul]
    rw [ENNReal.inv_two_add_inv_two, one_mul]
  exact (hf (2 * p)).fun_mul (hg (2 * p))

private lemma allLp_sum {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → Ω → ℝ) (hf : ∀ i ∈ s, AllLp μ (f i)) :
    AllLp μ (fun x => ∑ i ∈ s, f i x) := by
  intro p
  exact memLp_finsetSum _ (fun i hi => hf i hi p)

private lemma allLp_prod {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, AllLp μ (f i)) :
    AllLp μ (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro p; simpa using (memLp_const (1 : ℝ) (p := (p : ℝ≥0∞)))
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact allLp_mul (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private lemma sphere_cont_allLp (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ) (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : AllLp (μ) f := by
  letI := hμ.prob
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact
    (Set.Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => (1 : ℝ)))).bddAbove_image
      hf.norm.continuousOn
  intro p
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [hμ.sphere] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma monoVal_cont (s : Multiset (Fin n)) :
    Continuous (fun x : Fin n → ℝ => BstLean.Part36.monoVal x s) := by
  exact continuous_multiset_prod s (fun _ _ => continuous_apply _)

private lemma joint_map_allLp (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ) (hn : 1 ≤ n) (a : Fin n) :
    AllLp ((stdGauss (CoefIdxD n d)).prod (μ))
      (fun zx => BstLean.Part36.mapMD zx.1 zx.2 a) := by
  classical
  letI := hμ.prob
  unfold BstLean.Part36.mapMD
  apply allLp_sum
  intro i hi
  apply allLp_sum
  intro b _
  apply allLp_mul
  · intro p
    simp only [BstLean.Part36.coefD, Finset.mem_range.mp hi, dite_true]
    exact ((ProbabilityTheory.memLp_id_gaussianReal p).comp_measurePreserving
      (measurePreserving_eval (fun _ : CoefIdxD n d =>
        ProbabilityTheory.gaussianReal 0 1) ⟨⟨i, Finset.mem_range.mp hi⟩, b, a⟩)).comp_fst
          (μ)
  · intro p
    exact (sphere_cont_allLp μ hμ hn (monoVal_cont b.1) p).comp_snd (stdGauss (CoefIdxD n d))

private lemma joint_uJ_allLp (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ) (hn : 1 ≤ n) (T : Tens n) (j : ℕ) :
    AllLp ((stdGauss (CoefIdxD n d)).prod (μ))
      (fun zx => uJ T j zx.1 zx.2) := by
  classical
  letI := hμ.prob
  unfold uJ contr
  apply allLp_sum
  intro w _
  apply allLp_mul
  · intro p; exact memLp_const _
  · exact allLp_prod _ _ (fun t _ => joint_map_allLp μ hμ hn (w t))

private lemma joint_map_cont (a : Fin n) : Continuous
    (fun zx : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      BstLean.Part36.mapMD zx.1 zx.2 a) := by
  classical
  unfold BstLean.Part36.mapMD
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro b _
  simp only [BstLean.Part36.coefD, Finset.mem_range.mp hi, dite_true]
  exact (((continuous_apply _).comp continuous_fst).mul
    ((monoVal_cont b.1).comp continuous_snd))

lemma joint_uJ_cont (T : Tens n) (j : ℕ) : Continuous
    (fun zx : (CoefIdxD n d → ℝ) × (Fin n → ℝ) => uJ T j zx.1 zx.2) := by
  classical
  unfold uJ contr
  apply continuous_finsetSum
  intro w _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro t _
  exact joint_map_cont (w t)

private lemma uJ_cont (T : Tens n) (j : ℕ) (Z : CoefIdxD n d → ℝ) :
    Continuous (uJ T j Z) := by
  classical
  have hm (a : Fin n) : Continuous (fun x => BstLean.Part36.mapMD Z x a) := by
    unfold BstLean.Part36.mapMD
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro b _
    exact continuous_const.mul (monoVal_cont b.1)
  unfold uJ contr
  apply continuous_finsetSum
  intro w _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro t _
  exact hm (w t)

lemma varU_uJ_measurable (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ) (hn : 1 ≤ n) (T : Tens n) (j : ℕ) :
    Measurable (fun Z : CoefIdxD n d → ℝ =>
      varU (μ) (uJ T j Z)) := by
  letI := hμ.prob
  have hh := (joint_uJ_cont (d := d) T j).measurable
  have hm : Measurable (fun Z : CoefIdxD n d → ℝ =>
      ∫ x, uJ T j Z x ∂μ) :=
    hh.stronglyMeasurable.integral_prod_right'.measurable
  have hc := (hh.sub (hm.comp measurable_fst)).pow_const 2
  exact hc.stronglyMeasurable.integral_prod_right'.measurable

lemma varU_le_second (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h : (Fin n → ℝ) → ℝ) (hh : AEStronglyMeasurable h μ) :
    varU μ h ≤ ∫ x, h x ^ 2 ∂μ := by
  have hv := ProbabilityTheory.variance_eq_integral (μ := μ) (X := h) hh.aemeasurable
  exact hv.symm.le.trans (ProbabilityTheory.variance_le_expectation_sq hh)

lemma varU_uJ_integrable (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ) (hn : 1 ≤ n) (T : Tens n) (j : ℕ) :
    Integrable (fun Z : CoefIdxD n d → ℝ =>
      varU (μ) (uJ T j Z)) (stdGauss (CoefIdxD n d)) := by
  letI := hμ.prob
  have hi : Integrable (fun zx : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      uJ T j zx.1 zx.2 ^ 2)
      ((stdGauss (CoefIdxD n d)).prod (μ)) :=
    (joint_uJ_allLp μ hμ hn T j 2).integrable_sq
  apply hi.integral_prod_left.mono' (varU_uJ_measurable μ hμ hn T j).aestronglyMeasurable
  filter_upwards [] with Z
  have hv0 : 0 ≤ varU (μ) (uJ T j Z) :=
    integral_nonneg fun _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hv0]
  have hc := uJ_cont T j Z
  exact varU_le_second (μ) (uJ T j Z) hc.aestronglyMeasurable


lemma expected_var_le_raw (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ)
    (hn : 1 ≤ n) (T : Tens n) (j : ℕ) :
    (∫ Z : CoefIdxD n d → ℝ, varU μ (uJ T j Z) ∂stdGauss (CoefIdxD n d)) ≤
      ∫ x, ∫ Z : CoefIdxD n d → ℝ, uJ T j Z x ^ 2 ∂stdGauss (CoefIdxD n d) ∂μ := by
  let := hμ.prob
  have hi : Integrable (fun zx : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      uJ T j zx.1 zx.2 ^ 2) ((stdGauss (CoefIdxD n d)).prod μ) :=
    (joint_uJ_allLp μ hμ hn T j 2).integrable_sq
  have hb := integral_mono (varU_uJ_integrable μ hμ hn T j) hi.integral_prod_left
    (fun Z => varU_le_second μ (uJ T j Z) (uJ_cont T j Z).aestronglyMeasurable)
  exact hb.trans_eq (integral_integral_swap hi)

lemma raw_second_expectation_integrable (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ)
    (hn : 1 ≤ n) (T : Tens n) (j : ℕ) :
    Integrable (fun x => ∫ Z : CoefIdxD n d → ℝ, uJ T j Z x ^ 2
      ∂stdGauss (CoefIdxD n d)) μ := by
  let := hμ.prob
  have hi : Integrable (fun zx : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      uJ T j zx.1 zx.2 ^ 2) ((stdGauss (CoefIdxD n d)).prod μ) :=
    (joint_uJ_allLp μ hμ hn T j 2).integrable_sq
  exact hi.integral_prod_right

end BstLean.Part53.T2Aux
