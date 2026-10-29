import BstLean.Part140Norm
import BstLean.Part205Geometry

/-! Exact Gaussian row distance, with input averages under one sphere distribution. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 BstLean.Part105 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137

section
variable {N m : ℕ} (g : (Fin N → ℝ) → Fin m → ℝ)

noncomputable def rowInput (ξ : Fin m → ℝ) (u : Fin N → ℝ) : ℝ :=
  relu (dotp ξ (g u))

noncomputable def rowMean (ξ : Fin m → ℝ) : ℝ :=
  ∫ u, rowInput g ξ u ∂uniformSphere N

noncomputable def rowSmooth (h : Fin m → ℝ) (σ : ℝ) (ξ : Fin m → ℝ) : ℝ :=
  psiS σ (dotp ξ h)

noncomputable def rowDelta (h : Fin m → ℝ) (σ : ℝ) : ℝ :=
  (∫ p, kernelPhi (g p.1) (g p.2) ∂(uniformSphere N).prod (uniformSphere N)) -
    2 * (∫ u, kernelPhi (Fin.cons 0 (g u)) (Fin.cons σ h) ∂uniformSphere N) +
    kernelPhi (smoothP h σ) (smoothP' h σ)

lemma kernelPhi_pad_zero {k : ℕ} (x y : Fin k → ℝ) :
    kernelPhi (Fin.cons 0 x) (Fin.cons 0 y) = kernelPhi x y := by
  unfold kernelPhi
  rw [normSq_cons, normSq_cons, dotp_cons]
  simp

lemma kernelPhi_cross_two (x h : Fin m → ℝ) (σ : ℝ) :
    kernelPhi (Fin.cons 0 (Fin.cons 0 x)) (smoothP h σ) =
      kernelPhi (Fin.cons 0 x) (Fin.cons σ h) := by
  unfold kernelPhi smoothP
  simp only [normSq_cons, dotp_cons, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, zero_mul, zero_add]

/-- Put every term of the distance kernel into the same augmented vector space. -/
lemma rowDelta_two_coordinates (h : Fin m → ℝ) (σ : ℝ) :
    rowDelta g h σ =
      (∫ p, kernelPhi (Fin.cons 0 (Fin.cons 0 (g p.1)))
        (Fin.cons 0 (Fin.cons 0 (g p.2))) ∂(uniformSphere N).prod (uniformSphere N)) -
      2 * (∫ u, kernelPhi (Fin.cons 0 (Fin.cons 0 (g u))) (smoothP h σ)
        ∂uniformSphere N) + kernelPhi (smoothP h σ) (smoothP' h σ) := by
  simp only [kernelPhi_pad_zero, kernelPhi_cross_two, rowDelta]

lemma dotp_scale_right (c : ℝ) (ξ h : Fin m → ℝ) :
    dotp ξ (c • h) = c * dotp ξ h := by
  unfold dotp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma rowMean_scale {c : ℝ} (hc : 0 ≤ c) (ξ : Fin m → ℝ) :
    rowMean (fun u => c • g u) ξ = c * rowMean g ξ := by
  unfold rowMean rowInput
  simp_rw [dotp_scale_right, relu_mul_of_nonneg hc]
  rw [integral_const_mul]

lemma rowSmooth_scale {c : ℝ} (hc : 0 ≤ c) (h : Fin m → ℝ) (σ : ℝ)
    (ξ : Fin m → ℝ) :
    rowSmooth (c • h) (c * σ) ξ = c * rowSmooth h σ ξ := by
  unfold rowSmooth
  rw [dotp_scale_right, psiS_scale hc]

lemma rowInput_continuous (hg : Continuous g) :
    Continuous (fun p : (Fin m → ℝ) × (Fin N → ℝ) => rowInput g p.1 p.2) := by
  unfold rowInput
  exact continuous_relu.comp (continuous_dotp.comp (continuous_fst.prodMk
    (hg.comp continuous_snd)))

lemma rowMean_measurable (hg : Continuous g) : Measurable (rowMean g) :=
  (rowInput_continuous g hg).stronglyMeasurable.integral_prod_right'.measurable

lemma rowMean_nonneg (ξ : Fin m → ℝ) : 0 ≤ rowMean g ξ :=
  integral_nonneg fun _ => relu_nonneg _

/-- Jensen and a quadratic Gaussian majorant supply the square integrability. -/
lemma rowMean_sq_integrable (hN : 1 ≤ N) (hg : Continuous g) :
    Integrable (fun ξ => rowMean g ξ ^ 2) (stdGauss (Fin m)) := by
  have := uniformSphere_isProbability N hN
  let Q : ℝ := ∫ u, normSq (g u) ∂uniformSphere N
  have iQ : Integrable (fun u => normSq (g u)) (uniformSphere N) :=
    sphere_cont_integrable hN (continuous_normSq.comp hg)
  have hr : ∀ ξ, Integrable (fun u => rowInput g ξ u ^ 2) (uniformSphere N) :=
    fun ξ => sphere_cont_integrable hN
      (((rowInput_continuous g hg).comp (continuous_const.prodMk continuous_id)).pow 2)
  have hbound : ∀ ξ, rowMean g ξ ^ 2 ≤ normSq ξ * Q := by
    intro ξ
    refine (sq_integral_le (hr ξ)).trans ?_
    rw [← integral_const_mul]
    exact integral_mono (hr ξ) (iQ.const_mul _) fun u =>
      (relu_sq_le _).trans (by simpa [dotp] using dotL_sq_le ξ (g u))
  refine Integrable.mono' ((gauss_normSq m).1.mul_const Q)
    ((rowMean_measurable g hg).pow_const 2).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa [mul_comm] using hbound ξ

lemma rowSmooth_sq (h : Fin m → ℝ) (σ : ℝ) :
    Integrable (fun ξ => rowSmooth h σ ξ ^ 2) (stdGauss (Fin m)) ∧
      ∫ ξ, rowSmooth h σ ξ ^ 2 ∂stdGauss (Fin m) =
        kernelPhi (smoothP h σ) (smoothP' h σ) / 2 := by
  obtain ⟨hi, he, -, -⟩ := BstLean.Part140.sq_row (by norm_num : (0 : ℝ) < 1) σ h
  simpa [BstLean.Part140.fQ, BstLean.Part140.cQ, BstLean.Part140.hP1,
    BstLean.Part140.hP2, smoothP, smoothP', rowSmooth, dotp] using And.intro hi he

/-- The pair average keeps the same Gaussian row at both inputs. -/
lemma rowMean_sq_identity (hN : 1 ≤ N) (hg : Continuous g) :
    ∫ ξ, rowMean g ξ ^ 2 ∂stdGauss (Fin m) =
      (∫ p, kernelPhi (g p.1) (g p.2) ∂(uniformSphere N).prod (uniformSphere N)) / 2 := by
  have := uniformSphere_isProbability N hN
  let H : (Fin m → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ :=
    fun p => rowInput g p.1 p.2.1 * rowInput g p.1 p.2.2
  have hc : Continuous H := by
    exact ((rowInput_continuous g hg).comp (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd))).mul
      ((rowInput_continuous g hg).comp (continuous_fst.prodMk
        (continuous_snd.comp continuous_snd)))
  have hinner : ∀ ξ, ∫ p, H (ξ, p) ∂(uniformSphere N).prod (uniformSphere N) =
      rowMean g ξ ^ 2 := by
    intro ξ
    dsimp [H]
    rw [integral_prod_mul]
    simp only [rowMean, pow_two]
  have hi : Integrable H ((stdGauss (Fin m)).prod
      ((uniformSphere N).prod (uniformSphere N))) := by
    rw [integrable_prod_iff hc.aestronglyMeasurable]
    constructor
    · exact Filter.Eventually.of_forall fun ξ =>
        (sphere_cont_integrable hN ((rowInput_continuous g hg).comp
          (continuous_const.prodMk continuous_id))).mul_prod
        (sphere_cont_integrable hN ((rowInput_continuous g hg).comp
          (continuous_const.prodMk continuous_id)))
    · have hn : ∀ ξ p, ‖H (ξ, p)‖ = H (ξ, p) := fun ξ p =>
        Real.norm_of_nonneg (mul_nonneg (relu_nonneg _) (relu_nonneg _))
      simp_rw [hn, hinner]
      exact rowMean_sq_integrable g hN hg
  have he := integral_prod_symm H hi
  rw [integral_prod H hi] at he
  simp_rw [hinner] at he
  rw [he]
  have hp : ∀ p, ∫ ξ, H (ξ, p) ∂stdGauss (Fin m) =
      kernelPhi (g p.1) (g p.2) / 2 := by
    intro p
    simpa [H, rowInput, dotp] using
      (rowPair137 (by norm_num : (0 : ℝ) ≤ 1) (g p.1) (g p.2)).2.1
  simp_rw [hp]
  rw [integral_div]

lemma rowMean_smooth_integrable (hN : 1 ≤ N) (hg : Continuous g)
    (h : Fin m → ℝ) (σ : ℝ) :
    Integrable (fun ξ => rowMean g ξ * rowSmooth h σ ξ) (stdGauss (Fin m)) := by
  have hm : Measurable (rowSmooth h σ) := by
    unfold rowSmooth
    exact measurable_psiS.comp (measurable_const.prodMk
      ((continuous_dotp.comp (continuous_id.prodMk continuous_const)).measurable))
  refine Integrable.mono' ((rowMean_sq_integrable g hN hg).add (rowSmooth_sq h σ).1)
    ((rowMean_measurable g hg).mul hm).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ξ => ?_
  have hb : 0 ≤ rowSmooth h σ ξ := psiS_nonneg σ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (rowMean_nonneg g ξ) hb)]
  dsimp only [Pi.add_apply]
  nlinarith [sq_nonneg (rowMean g ξ - rowSmooth h σ ξ)]

lemma rowMean_smooth_identity (hN : 1 ≤ N) (hg : Continuous g)
    (h : Fin m → ℝ) (σ : ℝ) :
    ∫ ξ, rowMean g ξ * rowSmooth h σ ξ ∂stdGauss (Fin m) =
      (∫ u, kernelPhi (Fin.cons 0 (g u)) (Fin.cons σ h) ∂uniformSphere N) / 2 := by
  have := uniformSphere_isProbability N hN
  let H : (Fin m → ℝ) × (Fin N → ℝ) → ℝ :=
    fun p => rowInput g p.1 p.2 * rowSmooth h σ p.1
  have hm : Measurable (rowSmooth h σ) := by
    unfold rowSmooth
    exact measurable_psiS.comp (measurable_const.prodMk
      ((continuous_dotp.comp (continuous_id.prodMk continuous_const)).measurable))
  have hHm : Measurable H := (rowInput_continuous g hg).measurable.mul
    (hm.comp measurable_fst)
  have hinner : ∀ ξ, ∫ u, H (ξ, u) ∂uniformSphere N =
      rowMean g ξ * rowSmooth h σ ξ := by
    intro ξ
    dsimp [H]
    rw [integral_mul_const]
    rfl
  have hi : Integrable H ((stdGauss (Fin m)).prod (uniformSphere N)) := by
    rw [integrable_prod_iff hHm.aestronglyMeasurable]
    constructor
    · refine Filter.Eventually.of_forall fun ξ => ?_
      change Integrable (fun u => rowInput g ξ u * rowSmooth h σ ξ) (uniformSphere N)
      exact (sphere_cont_integrable hN ((rowInput_continuous g hg).comp
        (continuous_const.prodMk continuous_id))).mul_const (rowSmooth h σ ξ)
    · have hn : ∀ ξ u, ‖H (ξ, u)‖ = H (ξ, u) := fun ξ u =>
        Real.norm_of_nonneg (mul_nonneg (relu_nonneg _) (psiS_nonneg _ _))
      simp_rw [hn, hinner]
      exact rowMean_smooth_integrable g hN hg h σ
  have he := integral_prod_symm H hi
  rw [integral_prod H hi] at he
  simp_rw [hinner] at he
  rw [he]
  have hp : ∀ u, ∫ ξ, H (ξ, u) ∂stdGauss (Fin m) =
      kernelPhi (Fin.cons 0 (g u)) (Fin.cons σ h) / 2 := by
    intro u
    simpa [H, rowInput, rowSmooth, fS, cS, dotp] using
      (smooth_row (by norm_num : (0 : ℝ) < 1) σ (g u) h).2.1
  simp_rw [hp]
  rw [integral_div]

/-- The exact row identity retains cancellation between all three terms. -/
theorem exact_row_distance (hN : 1 ≤ N) (hg : Continuous g)
    (h : Fin m → ℝ) (σ : ℝ) :
    Integrable (fun ξ => (rowMean g ξ - rowSmooth h σ ξ) ^ 2) (stdGauss (Fin m)) ∧
      2 * (∫ ξ, (rowMean g ξ - rowSmooth h σ ξ) ^ 2 ∂stdGauss (Fin m)) =
        rowDelta g h σ := by
  have iA := rowMean_sq_integrable g hN hg
  have iB := (rowSmooth_sq h σ).1
  have iAB := rowMean_smooth_integrable g hN hg h σ
  have hexp : (fun ξ => (rowMean g ξ - rowSmooth h σ ξ) ^ 2) =
      fun ξ => rowMean g ξ ^ 2 - 2 * (rowMean g ξ * rowSmooth h σ ξ) +
        rowSmooth h σ ξ ^ 2 := by funext ξ; ring
  rw [hexp]
  have iC : Integrable (fun ξ => rowMean g ξ ^ 2 -
      2 * (rowMean g ξ * rowSmooth h σ ξ)) (stdGauss (Fin m)) :=
    iA.sub (iAB.const_mul 2)
  refine ⟨iC.add iB, ?_⟩
  rw [integral_add iC iB,
    integral_sub iA (iAB.const_mul 2), integral_const_mul,
    rowMean_sq_identity g hN hg, rowMean_smooth_identity g hN hg h σ,
    (rowSmooth_sq h σ).2]
  unfold rowDelta
  ring

end
end BstLean.Part205

#print axioms BstLean.Part205.rowMean_sq_integrable
#print axioms BstLean.Part205.rowSmooth_sq
#print axioms BstLean.Part205.rowMean_sq_identity
#print axioms BstLean.Part205.rowMean_smooth_identity
#print axioms BstLean.Part205.exact_row_distance
