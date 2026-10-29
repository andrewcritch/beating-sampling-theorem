import BstLean.Part154MFa
import BstLean.Part150Norm2

/-!
# Part 154: Lemma MF, Step 2 (the variance term) for a fixed value `a` of `ā`
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (relu reluV normSq)
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm)

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {f : Ω → Fin m → ℝ} {ℓ πg : ℝ}

open BstLean.Part153 (nrm_nonneg nrm_sq abs_dot_le_nrm)

/-! ## Auxiliary facts -/

section Aux

variable {k : ℕ}

/-- `E relu(x + ⟨z, g⟩) = ψ_{|g|}(x)`. -/
lemma relu_lin_int (x : ℝ) (g : Fin k → ℝ) :
    ∫ z, relu (x + z ⬝ᵥ g) ∂stdGauss (Fin k) = psiS (nrm g) x := by
  have h := BstLean.Part150.gauss_lin_integral g (f := fun t => relu (x + t))
    (BstLean.Part130.measurable_relu.comp (measurable_const.add measurable_id))
  rw [h]; rfl

lemma int_nrm_sq : Integrable (fun z : Fin k → ℝ => nrm z ^ 2) (stdGauss (Fin k)) := by
  have h := (BstLean.Part153.int_normSq_shift (0 : Fin k → ℝ) 1).1
  simpa [nrm_sq] using h

lemma meas_nrm : Measurable (fun z : Fin k → ℝ => nrm z) :=
  BstLean.Part130.measurable_normSq.sqrt

lemma int_nrm : Integrable (fun z : Fin k → ℝ => nrm z) (stdGauss (Fin k)) := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add int_nrm_sq)
    meas_nrm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (nrm_nonneg z)]
  show nrm z ≤ 1 + nrm z ^ 2
  nlinarith [sq_nonneg (nrm z - 1)]

lemma relu_lin_abs (x : ℝ) (z g : Fin k → ℝ) : |relu (x + z ⬝ᵥ g)| ≤ |x| + nrm z * nrm g :=
  (BstLean.Part130.abs_relu_le _).trans
    ((abs_add_le _ _).trans (add_le_add le_rfl (abs_dot_le_nrm z g)))

lemma meas_dotV {α : Type*} [MeasurableSpace α] {u v : α → Fin k → ℝ} (hu : Measurable u)
    (hv : Measurable v) : Measurable (fun x => u x ⬝ᵥ v x) := by
  show Measurable (fun x => ∑ i, u x i * v x i)
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hu).mul ((measurable_pi_apply i).comp hv)

lemma meas_PhiG : Measurable PhiG :=
  (continuous_iff_continuousAt.2 fun v =>
    (BstLean.Part153.hasDerivAt_PhiG v).continuousAt).measurable

end Aux

/-- `r_ω(z′) = relu(β(ω)a + ⟨z′, Π f(ω)⟩)`. -/
noncomputable abbrev rrF (μ : Measure Ω) (f : Ω → Fin m → ℝ) (a : ℝ) (ω : Ω) (z : Fin m → ℝ) : ℝ :=
  relu (betaF μ f ω * a + z ⬝ᵥ gF μ f ω)

/-- `ς(ω) = |Π f(ω)|`. -/
noncomputable abbrev sgF (μ : Measure Ω) (f : Ω → Fin m → ℝ) (ω : Ω) : ℝ := nrm (gF μ f ω)

/-- `ψ_ς(βa)`. -/
noncomputable abbrev psF (μ : Measure Ω) (f : Ω → Fin m → ℝ) (a : ℝ) (ω : Ω) : ℝ :=
  psiS (nrm (gF μ f ω)) (betaF μ f ω * a)

/-- `p(ω) = Φ(β a/ς)`. -/
noncomputable abbrev ppF (μ : Measure Ω) (f : Ω → Fin m → ℝ) (a : ℝ) (ω : Ω) : ℝ :=
  PhiG (betaF μ f ω * a / nrm (gF μ f ω))

/-- `𝖼(ω, ω′)`. -/
noncomputable abbrev ccF (μ : Measure Ω) (f : Ω → Fin m → ℝ) (p : Ω × Ω) : ℝ := gF μ f p.1 ⬝ᵥ gF μ f p.2

/-- `𝖼²/(ςς′)`. -/
noncomputable abbrev rsF (μ : Measure Ω) (f : Ω → Fin m → ℝ) (p : Ω × Ω) : ℝ :=
  ccF μ f p ^ 2 / (nrm (gF μ f p.1) * nrm (gF μ f p.2))

lemma MFHyp.meas_rr (H : MFHyp μ f ℓ πg) (a : ℝ) :
    Measurable (fun q : Ω × (Fin m → ℝ) => rrF μ f a q.1 q.2) :=
  BstLean.Part130.measurable_relu.comp
    (((H.meas_beta.comp measurable_fst).mul_const a).add
      (meas_dotV measurable_snd (H.meas_g.comp measurable_fst)))

lemma MFHyp.int_sg (H : MFHyp μ f ℓ πg) : Integrable (fun ω => sgF μ f ω) μ := H.sig_int.1

lemma MFHyp.int_ba (H : MFHyp μ f ℓ πg) (a : ℝ) : Integrable (fun ω => |betaF μ f ω * a|) μ :=
  (H.F1.1.mul_const a).abs

lemma MFHyp.rInt (H : MFHyp μ f ℓ πg) (a : ℝ) :
    Integrable (fun q : Ω × (Fin m → ℝ) => rrF μ f a q.1 q.2) (μ.prod (stdGauss (Fin m))) := by
  have d1 : Integrable (fun q : Ω × (Fin m → ℝ) => |betaF μ f q.1 * a|)
      (μ.prod (stdGauss (Fin m))) := (H.int_ba a).comp_fst _
  have d2 : Integrable (fun q : Ω × (Fin m → ℝ) => sgF μ f q.1 * nrm q.2)
      (μ.prod (stdGauss (Fin m))) := H.int_sg.mul_prod int_nrm
  refine Integrable.mono' (d1.add d2) (H.meas_rr a).aestronglyMeasurable (ae_of_all _ fun q => ?_)
  rw [Real.norm_eq_abs]
  show |rrF μ f a q.1 q.2| ≤ |betaF μ f q.1 * a| + nrm (gF μ f q.1) * nrm q.2
  rw [mul_comm (nrm (gF μ f q.1))]
  exact relu_lin_abs _ _ _

lemma MFHyp.HInt (H : MFHyp μ f ℓ πg) (a : ℝ) :
    Integrable (fun q : (Ω × Ω) × (Fin m → ℝ) => rrF μ f a q.1.1 q.2 * rrF μ f a q.1.2 q.2)
      ((μ.prod μ).prod (stdGauss (Fin m))) := by
  have hb := H.int_ba a
  have hs := H.int_sg
  have d1 : Integrable (fun q : (Ω × Ω) × (Fin m → ℝ) =>
      |betaF μ f q.1.1 * a| * |betaF μ f q.1.2 * a|) ((μ.prod μ).prod (stdGauss (Fin m))) :=
    (hb.mul_prod hb).comp_fst _
  have d2 : Integrable (fun q : (Ω × Ω) × (Fin m → ℝ) =>
      |betaF μ f q.1.1 * a| * sgF μ f q.1.2 * nrm q.2) ((μ.prod μ).prod (stdGauss (Fin m))) :=
    (hb.mul_prod hs).mul_prod int_nrm
  have d3 : Integrable (fun q : (Ω × Ω) × (Fin m → ℝ) =>
      sgF μ f q.1.1 * |betaF μ f q.1.2 * a| * nrm q.2) ((μ.prod μ).prod (stdGauss (Fin m))) :=
    (hs.mul_prod hb).mul_prod int_nrm
  have d4 : Integrable (fun q : (Ω × Ω) × (Fin m → ℝ) =>
      sgF μ f q.1.1 * sgF μ f q.1.2 * nrm q.2 ^ 2) ((μ.prod μ).prod (stdGauss (Fin m))) :=
    (hs.mul_prod hs).mul_prod int_nrm_sq
  have hm : Measurable (fun q : (Ω × Ω) × (Fin m → ℝ) =>
      rrF μ f a q.1.1 q.2 * rrF μ f a q.1.2 q.2) :=
    ((H.meas_rr a).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      ((H.meas_rr a).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  refine Integrable.mono' (((d1.add d2).add d3).add d4) hm.aestronglyMeasurable
    (ae_of_all _ fun q => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := relu_lin_abs (betaF μ f q.1.1 * a) q.2 (gF μ f q.1.1)
  have h2 := relu_lin_abs (betaF μ f q.1.2 * a) q.2 (gF μ f q.1.2)
  have n0 := nrm_nonneg q.2
  have n1 := nrm_nonneg (gF μ f q.1.1)
  have n2 := nrm_nonneg (gF μ f q.1.2)
  show |rrF μ f a q.1.1 q.2| * |rrF μ f a q.1.2 q.2| ≤
    |betaF μ f q.1.1 * a| * |betaF μ f q.1.2 * a| +
      |betaF μ f q.1.1 * a| * nrm (gF μ f q.1.2) * nrm q.2 +
      nrm (gF μ f q.1.1) * |betaF μ f q.1.2 * a| * nrm q.2 +
      nrm (gF μ f q.1.1) * nrm (gF μ f q.1.2) * nrm q.2 ^ 2
  calc |rrF μ f a q.1.1 q.2| * |rrF μ f a q.1.2 q.2|
      ≤ (|betaF μ f q.1.1 * a| + nrm q.2 * nrm (gF μ f q.1.1)) *
        (|betaF μ f q.1.2 * a| + nrm q.2 * nrm (gF μ f q.1.2)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (add_nonneg (abs_nonneg _) (mul_nonneg n0 n1))
    _ = _ := by ring

/-- `0 ≤ 𝖼²/(ςς′) ≤ ςς′`. -/
lemma rsF_bd (μ : Measure Ω) (f : Ω → Fin m → ℝ) (p : Ω × Ω) :
    0 ≤ rsF μ f p ∧ rsF μ f p ≤ sgF μ f p.1 * sgF μ f p.2 := by
  have hc := abs_dot_le_nrm (gF μ f p.1) (gF μ f p.2)
  have hn : 0 ≤ nrm (gF μ f p.1) * nrm (gF μ f p.2) := mul_nonneg (nrm_nonneg _) (nrm_nonneg _)
  have hc2 : ccF μ f p ^ 2 ≤ (nrm (gF μ f p.1) * nrm (gF μ f p.2)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  refine ⟨div_nonneg (sq_nonneg _) hn, ?_⟩
  show ccF μ f p ^ 2 / (nrm (gF μ f p.1) * nrm (gF μ f p.2)) ≤
    nrm (gF μ f p.1) * nrm (gF μ f p.2)
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · rw [div_le_iff₀ hpos]
    calc ccF μ f p ^ 2 ≤ (nrm (gF μ f p.1) * nrm (gF μ f p.2)) ^ 2 := hc2
      _ = _ := sq _

/-- The integral of `𝖼²/(ςς′)`. -/
lemma MFHyp.rs_int (H : MFHyp μ f ℓ πg) :
    Integrable (fun p : Ω × Ω => rsF μ f p) (μ.prod μ) ∧
    ∫ p : Ω × Ω, rsF μ f p ∂(μ.prod μ) ≤ 2 * hsF μ f / sF2 μ f + √2 * sF2 μ f * πg := by
  classical
  have hsg := H.int_sg
  have hss : Integrable (fun p : Ω × Ω => sgF μ f p.1 * sgF μ f p.2) (μ.prod μ) :=
    hsg.mul_prod hsg
  have hm : Measurable (fun p : Ω × Ω => rsF μ f p) :=
    ((meas_dotV (H.meas_g.comp measurable_fst) (H.meas_g.comp measurable_snd)).pow_const 2).div
      ((meas_nrm.comp (H.meas_g.comp measurable_fst)).mul
        (meas_nrm.comp (H.meas_g.comp measurable_snd)))
  have hRi : Integrable (fun p : Ω × Ω => rsF μ f p) (μ.prod μ) :=
    Integrable.mono' hss hm.aestronglyMeasurable (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (rsF_bd μ f p).1]; exact (rsF_bd μ f p).2)
  refine ⟨hRi, ?_⟩
  obtain ⟨hs0, hs2⟩ := H.sF_pos
  obtain ⟨-, hsle, hsB⟩ := H.sig_int
  obtain ⟨hc2i, hc2le⟩ := H.F4c
  have hspos := H.hs
  set B : Set Ω := {ω | sig2F μ f ω < sF2 μ f / 2} with hBdef
  have hB : MeasurableSet B := measurableSet_lt H.meas_sig measurable_const
  have hiB : Integrable (fun ω => B.indicator (fun ω => sgF μ f ω) ω) μ := hsg.indicator hB
  have hind0 : ∀ ω, 0 ≤ B.indicator (fun ω => sgF μ f ω) ω := fun ω =>
    Set.indicator_nonneg (fun _ _ => nrm_nonneg _) _
  have hRb : ∀ p : Ω × Ω, rsF μ f p ≤ 2 / sF2 μ f * ccF μ f p ^ 2 +
      (B.indicator (fun ω => sgF μ f ω) p.1 * sgF μ f p.2 +
        sgF μ f p.1 * B.indicator (fun ω => sgF μ f ω) p.2) := by
    intro p
    have t0 : 0 ≤ 2 / sF2 μ f * ccF μ f p ^ 2 :=
      mul_nonneg (div_nonneg zero_le_two hspos.le) (sq_nonneg _)
    have hle := (rsF_bd μ f p).2
    have s1 : 0 ≤ sgF μ f p.1 := nrm_nonneg _
    have s2 : 0 ≤ sgF μ f p.2 := nrm_nonneg _
    have i1 := hind0 p.1
    have i2 := hind0 p.2
    by_cases h1 : p.1 ∈ B
    · rw [Set.indicator_of_mem h1]
      have := mul_nonneg s1 i2
      linarith
    by_cases h2 : p.2 ∈ B
    · rw [Set.indicator_of_mem h2]
      have := mul_nonneg i1 s2
      linarith
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    have a1 : sF2 μ f / 2 ≤ nrm (gF μ f p.1) ^ 2 := by rw [nrm_sq]; exact not_lt.1 h1
    have a2 : sF2 μ f / 2 ≤ nrm (gF μ f p.2) ^ 2 := by rw [nrm_sq]; exact not_lt.1 h2
    have hn : 0 ≤ nrm (gF μ f p.1) * nrm (gF μ f p.2) := mul_nonneg s1 s2
    have hD : sF2 μ f / 2 ≤ nrm (gF μ f p.1) * nrm (gF μ f p.2) := by
      by_contra hlt
      rw [not_le] at hlt
      have h3 : (nrm (gF μ f p.1) * nrm (gF μ f p.2)) ^ 2 < (sF2 μ f / 2) ^ 2 :=
        pow_lt_pow_left₀ hlt hn two_ne_zero
      have h4 : (sF2 μ f / 2) ^ 2 ≤ (nrm (gF μ f p.1) * nrm (gF μ f p.2)) ^ 2 := by
        rw [mul_pow, sq (sF2 μ f / 2)]
        exact mul_le_mul a1 a2 (by linarith) (sq_nonneg _)
      linarith
    have hDpos : 0 < nrm (gF μ f p.1) * nrm (gF μ f p.2) := lt_of_lt_of_le (by linarith) hD
    have h5 : 1 ≤ 2 / sF2 μ f * (nrm (gF μ f p.1) * nrm (gF μ f p.2)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hspos]; linarith
    have h6 : rsF μ f p ≤ 2 / sF2 μ f * ccF μ f p ^ 2 := by
      show ccF μ f p ^ 2 / (nrm (gF μ f p.1) * nrm (gF μ f p.2)) ≤ _
      rw [div_le_iff₀ hDpos]
      nlinarith [sq_nonneg (ccF μ f p)]
    simp only [zero_mul, mul_zero, add_zero]
    exact h6
  have hU1 : Integrable (fun p : Ω × Ω => 2 / sF2 μ f * ccF μ f p ^ 2) (μ.prod μ) :=
    hc2i.const_mul _
  have hU2 : Integrable (fun p : Ω × Ω => B.indicator (fun ω => sgF μ f ω) p.1 * sgF μ f p.2)
      (μ.prod μ) := hiB.mul_prod hsg
  have hU3 : Integrable (fun p : Ω × Ω => sgF μ f p.1 * B.indicator (fun ω => sgF μ f ω) p.2)
      (μ.prod μ) := hsg.mul_prod hiB
  have hIB : ∫ ω, B.indicator (fun ω => sgF μ f ω) ω ∂μ = ∫ ω in B, sgF μ f ω ∂μ :=
    integral_indicator hB
  have hIB0 : 0 ≤ ∫ ω, B.indicator (fun ω => sgF μ f ω) ω ∂μ := integral_nonneg hind0
  have hIBle : ∫ ω, B.indicator (fun ω => sgF μ f ω) ω ∂μ ≤ sF μ f / √2 * πg := by
    rw [hIB]; exact hsB
  have hIS0 : 0 ≤ ∫ ω, sgF μ f ω ∂μ := integral_nonneg fun ω => nrm_nonneg _
  have hISle : ∫ ω, sgF μ f ω ∂μ ≤ sF μ f := hsle
  have hw : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have hw0 : (0 : ℝ) < √2 := by positivity
  have hinv : 1 / √2 = √2 / 2 := by
    rw [div_eq_div_iff hw0.ne' (by norm_num)]; linarith
  have hb0 : 0 ≤ sF μ f / √2 * πg := mul_nonneg (div_nonneg hs0.le hw0.le) H.hπ0
  have hprod : (∫ ω, B.indicator (fun ω => sgF μ f ω) ω ∂μ) * (∫ ω, sgF μ f ω ∂μ) ≤
      √2 / 2 * sF2 μ f * πg := by
    calc (∫ ω, B.indicator (fun ω => sgF μ f ω) ω ∂μ) * (∫ ω, sgF μ f ω ∂μ)
        ≤ sF μ f / √2 * πg * sF μ f := mul_le_mul hIBle hISle hIS0 hb0
      _ = √2 / 2 * sF2 μ f * πg := by
          rw [div_eq_mul_one_div, hinv, ← hs2]; ring
  calc ∫ p : Ω × Ω, rsF μ f p ∂(μ.prod μ)
      ≤ ∫ p : Ω × Ω, (2 / sF2 μ f * ccF μ f p ^ 2 +
          (B.indicator (fun ω => sgF μ f ω) p.1 * sgF μ f p.2 +
            sgF μ f p.1 * B.indicator (fun ω => sgF μ f ω) p.2)) ∂(μ.prod μ) :=
        integral_mono hRi (hU1.add (hU2.add hU3)) hRb
    _ = 2 / sF2 μ f * ∫ p : Ω × Ω, ccF μ f p ^ 2 ∂(μ.prod μ) +
          ((∫ ω, B.indicator (fun ω => sgF μ f ω) ω ∂μ) * (∫ ω, sgF μ f ω ∂μ) +
            (∫ ω, sgF μ f ω ∂μ) * (∫ ω, B.indicator (fun ω => sgF μ f ω) ω ∂μ)) := by
        have hU23 : Integrable (fun p : Ω × Ω =>
            B.indicator (fun ω => sgF μ f ω) p.1 * sgF μ f p.2 +
              sgF μ f p.1 * B.indicator (fun ω => sgF μ f ω) p.2) (μ.prod μ) := hU2.add hU3
        rw [integral_add hU1 hU23, integral_add hU2 hU3, integral_const_mul,
          integral_prod_mul (fun ω => B.indicator (fun ω => sgF μ f ω) ω) (fun ω => sgF μ f ω),
          integral_prod_mul (fun ω => sgF μ f ω) (fun ω => B.indicator (fun ω => sgF μ f ω) ω)]
    _ ≤ 2 / sF2 μ f * hsF μ f + (√2 / 2 * sF2 μ f * πg + √2 / 2 * sF2 μ f * πg) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hc2le (div_nonneg zero_le_two hspos.le))
          (add_le_add hprod ?_)
        rw [mul_comm]; exact hprod
    _ = 2 * hsF μ f / sF2 μ f + √2 * sF2 μ f * πg := by ring

/-- The linear term. -/
lemma MFHyp.lin_int (H : MFHyp μ f ℓ πg) (a p0 : ℝ) :
    Integrable (fun p : Ω × Ω => ccF μ f p * ppF μ f a p.1 * ppF μ f a p.2) (μ.prod μ) ∧
    ∫ p : Ω × Ω, ccF μ f p * ppF μ f a p.1 * ppF μ f a p.2 ∂(μ.prod μ) ≤
      ℓ ^ 2 * ∫ ω, (ppF μ f a ω - p0) ^ 2 ∂μ := by
  have hPm : Measurable (fun ω => ppF μ f a ω) :=
    meas_PhiG.comp ((H.meas_beta.mul_const a).div (meas_nrm.comp H.meas_g))
  have hφ2 : Integrable (fun ω => (ppF μ f a ω - p0) ^ 2) μ := by
    refine Integrable.mono' (integrable_const ((1 + |p0|) ^ 2))
      ((hPm.sub_const p0).pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h0 := (BstLean.Part153.PhiG_pos (betaF μ f ω * a / nrm (gF μ f ω))).le
    have h1 := BstLean.Part153.PhiG_le_one (betaF μ f ω * a / nrm (gF μ f ω))
    have h2 : |ppF μ f a ω - p0| ≤ 1 + |p0| := by
      rw [abs_le]; constructor <;> cases abs_cases p0 <;> linarith
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  obtain ⟨hφg, hF4b⟩ := H.F4b (hPm.sub_const p0) hφ2
  have hPg : ∀ i, Integrable (fun ω => ppF μ f a ω * gF μ f ω i) μ := fun i => by
    have h := (hφg i).add ((H.F4a i).1.const_mul p0)
    refine h.congr (ae_of_all _ fun ω => ?_)
    show (ppF μ f a ω - p0) * gF μ f ω i + p0 * gF μ f ω i = ppF μ f a ω * gF μ f ω i
    ring
  have hPg0 : ∀ i, ∫ ω, (ppF μ f a ω - p0) * gF μ f ω i ∂μ =
      ∫ ω, ppF μ f a ω * gF μ f ω i ∂μ := fun i => by
    have e : ∀ ω, (ppF μ f a ω - p0) * gF μ f ω i =
        ppF μ f a ω * gF μ f ω i - p0 * gF μ f ω i := fun ω => by ring
    rw [integral_congr_ae (ae_of_all _ e),
      integral_sub (hPg i) ((H.F4a i).1.const_mul p0), integral_const_mul, (H.F4a i).2]
    ring
  have hT1e : ∀ p : Ω × Ω, ccF μ f p * ppF μ f a p.1 * ppF μ f a p.2 =
      ∑ i, (ppF μ f a p.1 * gF μ f p.1 i) * (ppF μ f a p.2 * gF μ f p.2 i) := fun p => by
    show (gF μ f p.1 ⬝ᵥ gF μ f p.2) * ppF μ f a p.1 * ppF μ f a p.2 = _
    simp only [dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsi : Integrable (fun p : Ω × Ω =>
      ∑ i, (ppF μ f a p.1 * gF μ f p.1 i) * (ppF μ f a p.2 * gF μ f p.2 i)) (μ.prod μ) :=
    integrable_finsetSum _ fun i _ => (hPg i).mul_prod (hPg i)
  refine ⟨hsi.congr (ae_of_all _ fun p => (hT1e p).symm), ?_⟩
  calc ∫ p : Ω × Ω, ccF μ f p * ppF μ f a p.1 * ppF μ f a p.2 ∂(μ.prod μ)
      = ∫ p : Ω × Ω, ∑ i, (ppF μ f a p.1 * gF μ f p.1 i) * (ppF μ f a p.2 * gF μ f p.2 i)
          ∂(μ.prod μ) := integral_congr_ae (ae_of_all _ hT1e)
    _ = ∑ i, (∫ ω, (ppF μ f a ω - p0) * gF μ f ω i ∂μ) ^ 2 := by
        rw [integral_finsetSum _ fun i _ => (hPg i).mul_prod (hPg i)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hPg0 i, sq]
        exact integral_prod_mul (fun ω => ppF μ f a ω * gF μ f ω i)
          (fun ω => ppF μ f a ω * gF μ f ω i)
    _ ≤ ℓ ^ 2 * ∫ ω, (ppF μ f a ω - p0) ^ 2 ∂μ := hF4b

/-- `E_{z′} Y_a = E_ω 𝒢(β a, ς²)`. -/
theorem MFHyp.YF_mean (H : MFHyp μ f ℓ πg) (a : ℝ) :
    Integrable (YF μ f a) (stdGauss (Fin m)) ∧
    Integrable (fun ω => psiS (√(sig2F μ f ω)) (betaF μ f ω * a)) μ ∧
    ∫ z', YF μ f a z' ∂stdGauss (Fin m) =
      ∫ ω, psiS (√(sig2F μ f ω)) (betaF μ f ω * a) ∂μ := by
  have hF := H.rInt a
  have hpt : ∀ ω, ∫ z, rrF μ f a ω z ∂stdGauss (Fin m) =
      psiS (√(sig2F μ f ω)) (betaF μ f ω * a) := fun ω => relu_lin_int _ _
  refine ⟨?_, ?_, ?_⟩
  · show Integrable (fun z' => ∫ ω, rrF μ f a ω z' ∂μ) (stdGauss (Fin m))
    exact hF.integral_prod_right
  · exact hF.integral_prod_left.congr (ae_of_all _ hpt)
  · calc ∫ z', YF μ f a z' ∂stdGauss (Fin m)
        = ∫ z', ∫ ω, rrF μ f a ω z' ∂μ ∂stdGauss (Fin m) := rfl
      _ = ∫ ω, ∫ z', rrF μ f a ω z' ∂stdGauss (Fin m) ∂μ :=
          (integral_integral_swap (f := fun ω z' => rrF μ f a ω z') hF).symm
      _ = _ := integral_congr_ae (ae_of_all _ hpt)

/-- **The variance term** for a fixed `a`, with an arbitrary number `p₀`. -/
theorem MFHyp.YF_var_le (H : MFHyp μ f ℓ πg) {K : ℝ} (hK0 : 0 ≤ K) (hPR : PRvecBound K)
    (a p0 : ℝ) :
    Integrable (fun z' => (YF μ f a z' - ∫ z'', YF μ f a z'' ∂stdGauss (Fin m)) ^ 2)
      (stdGauss (Fin m)) ∧
    ∫ z', (YF μ f a z' - ∫ z'', YF μ f a z'' ∂stdGauss (Fin m)) ^ 2 ∂stdGauss (Fin m) ≤
      ℓ ^ 2 * ∫ ω, (PhiG (betaF μ f ω * a / √(sig2F μ f ω)) - p0) ^ 2 ∂μ +
        K * (2 * hsF μ f / sF2 μ f + √2 * sF2 μ f * πg) := by
  obtain ⟨hYi, hψi, hEY⟩ := H.YF_mean a
  have hH := H.HInt a
  obtain ⟨hRi, hRle⟩ := H.rs_int
  obtain ⟨hT1i, hT1le⟩ := H.lin_int a p0
  generalize hE : (∫ z'', YF μ f a z'' ∂stdGauss (Fin m)) = EY at hEY ⊢
  have hY2 : ∀ z, YF μ f a z ^ 2 =
      ∫ p : Ω × Ω, rrF μ f a p.1 z * rrF μ f a p.2 z ∂(μ.prod μ) := fun z => by
    rw [sq]
    exact (integral_prod_mul (μ := μ) (ν := μ) (fun ω => rrF μ f a ω z)
      (fun ω => rrF μ f a ω z)).symm
  have hY2i : Integrable (fun z => YF μ f a z ^ 2) (stdGauss (Fin m)) :=
    hH.integral_prod_right.congr (ae_of_all _ fun z => (hY2 z).symm)
  have e : ∀ z, (YF μ f a z - EY) ^ 2 = YF μ f a z ^ 2 - 2 * EY * YF μ f a z + EY ^ 2 :=
    fun z => by ring
  have hint : Integrable (fun z => (YF μ f a z - EY) ^ 2) (stdGauss (Fin m)) :=
    ((hY2i.sub (hYi.const_mul (2 * EY))).add (integrable_const (EY ^ 2))).congr
      (ae_of_all _ fun z => (e z).symm)
  refine ⟨hint, ?_⟩
  have hvar : ∫ z, (YF μ f a z - EY) ^ 2 ∂stdGauss (Fin m) =
      ∫ z, YF μ f a z ^ 2 ∂stdGauss (Fin m) - EY ^ 2 := by
    have hA : Integrable (fun z => YF μ f a z ^ 2 - 2 * EY * YF μ f a z) (stdGauss (Fin m)) :=
      hY2i.sub (hYi.const_mul (2 * EY))
    rw [integral_congr_ae (ae_of_all _ e), integral_add hA (integrable_const (EY ^ 2)),
      integral_sub hY2i (hYi.const_mul (2 * EY)), integral_const_mul, integral_const, hE]
    simp
    ring
  have hψψ : Integrable (fun p : Ω × Ω => psF μ f a p.1 * psF μ f a p.2) (μ.prod μ) :=
    hψi.mul_prod hψi
  have hE2 : EY ^ 2 = ∫ p : Ω × Ω, psF μ f a p.1 * psF μ f a p.2 ∂(μ.prod μ) := by
    rw [sq, hEY]
    exact (integral_prod_mul (μ := μ) (ν := μ) (fun ω => psF μ f a ω)
      (fun ω => psF μ f a ω)).symm
  have hCi : Integrable (fun p : Ω × Ω =>
      ∫ z, rrF μ f a p.1 z * rrF μ f a p.2 z ∂stdGauss (Fin m)) (μ.prod μ) :=
    hH.integral_prod_left
  have hsw : ∫ z, YF μ f a z ^ 2 ∂stdGauss (Fin m) =
      ∫ p : Ω × Ω, ∫ z, rrF μ f a p.1 z * rrF μ f a p.2 z ∂stdGauss (Fin m) ∂(μ.prod μ) := by
    rw [integral_congr_ae (ae_of_all _ hY2)]
    exact (integral_integral_swap
      (f := fun (p : Ω × Ω) (z : Fin m → ℝ) => rrF μ f a p.1 z * rrF μ f a p.2 z) hH).symm
  have hV : ∫ z, (YF μ f a z - EY) ^ 2 ∂stdGauss (Fin m) =
      ∫ p : Ω × Ω, (∫ z, rrF μ f a p.1 z * rrF μ f a p.2 z ∂stdGauss (Fin m) -
        psF μ f a p.1 * psF μ f a p.2) ∂(μ.prod μ) := by
    rw [hvar, hsw, hE2, integral_sub hCi hψψ]
  have hpt : ∀ p : Ω × Ω, ∫ z, rrF μ f a p.1 z * rrF μ f a p.2 z ∂stdGauss (Fin m) -
        psF μ f a p.1 * psF μ f a p.2 ≤
      ccF μ f p * ppF μ f a p.1 * ppF μ f a p.2 + K * rsF μ f p := fun p => by
    have h := hPR m (gF μ f p.1) (gF μ f p.2) (betaF μ f p.1 * a) (betaF μ f p.2 * a)
    have h' := mul_div_assoc K (ccF μ f p ^ 2) (nrm (gF μ f p.1) * nrm (gF μ f p.2))
    rw [h'] at h
    exact h
  rw [hV]
  calc ∫ p : Ω × Ω, (∫ z, rrF μ f a p.1 z * rrF μ f a p.2 z ∂stdGauss (Fin m) -
        psF μ f a p.1 * psF μ f a p.2) ∂(μ.prod μ)
      ≤ ∫ p : Ω × Ω, (ccF μ f p * ppF μ f a p.1 * ppF μ f a p.2 + K * rsF μ f p)
          ∂(μ.prod μ) := integral_mono (hCi.sub hψψ) (hT1i.add (hRi.const_mul K)) hpt
    _ = ∫ p : Ω × Ω, ccF μ f p * ppF μ f a p.1 * ppF μ f a p.2 ∂(μ.prod μ) +
          K * ∫ p : Ω × Ω, rsF μ f p ∂(μ.prod μ) := by
        rw [integral_add hT1i (hRi.const_mul K), integral_const_mul]
    _ ≤ _ := add_le_add hT1le (mul_le_mul_of_nonneg_left hRle hK0)

end BstLean.Part154
