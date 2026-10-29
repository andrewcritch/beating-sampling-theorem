import BstLean.Part139Tools

/-!
# Part 139, item 2: a lower bound of the realized spread, with probability

Role: `delegations/statements/p139-spec.md`, item 2. Paper source: `onW6c-cx.md` §§3–4 (the
second moment of the realized spread over the Gaussian last row of `F`; the centring projection;
here with Chebyshev's inequality in the place of Cantelli's inequality, and with the input
distribution `μ_W` itself, not the stand-in).

Notation: `S = 4/n`, `Q = κ^{∘6}(0)`, `r = (W, (A, (A′, F)))` a point of `lawR` (Part 132; the
copy `A′` is not used here), `α = 2/m_F`, `C = covMat W A F₁ F₂` (Part 131).

* `gaussRow_qform_sq`: `E_{F₃}(wᵀCw − c)² = (α·tr C − c)² + 2α²·Σ_{ij} C_{ij}²`, `w` the row of
  the last matrix `F₃` of `F`.
* `tr_eq`, `frob_le`: `α·tr C = E_u k(u, u) − E_{u,u′} k(u, u′)` and
  `α²·Σ C_{ij}² ≤ E_{u,u′}(k(u, u′) − c)²` for every constant `c` (the kernel `k` of Part 132).
* `cond_sq`: for fixed `(W, A, F₁, F₂)`:
  `E_{F₃}(sd² − c)² ≤ (VS − PS − c)² + 2·E_{u,u′}(k − c₁)²`.
* **`spread_L2`**: from the `L²` bounds `‖k − c_P‖₂ ≤ e_P`, `‖k_diag − c_D‖₂ ≤ e_D` of the two
  kernels: `E_{W,A,F}(sd² − (c_D − c_P))² ≤ (e_D + e_P)² + 2·e_P²`.
* **`spreadLow_general`**: Chebyshev: `Pr(sd² < θ·y) ≤ ((e_D + e_P)² + 2e_P²)/((1 − θ)·y)²`,
  `y = c_D − c_P > 0`.
* **`spreadLow139`** (item 2): at the widths of the Focus, `n ≥ 4096`, `0 ≤ θ < 1`:
  `Pr(sd² < θ·S·(1 − Q)) ≤ ((e_V + e_P)² + 2e_P²)/((1 − θ)(1 − Q))²` with the constants `e_P`,
  `e_V` of Part 133; `spreadLow139_num`: with `e_P ≤ 0.06369`, `e_V ≤ 0.023`, `1 − Q ≥ 0.222`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part139

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133

section general

variable {N mW n mA mF : ℕ}

/-! ## The second moment of the quadratic form in the last row of `F` -/

lemma covMat_symm (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ) :
    (covMat W A F₁ F₂).transpose = covMat W A F₁ F₂ := by
  ext i j
  simp only [covMat, transpose_apply, of_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- `E(wᵀCw − c)² = (α·tr C − c)² + 2α²·Σ C_{ij}²` for the row `w` of a Gaussian matrix with one
row and entry variance `α`, and a symmetric `C`. -/
lemma gaussRow_qform_sq (α : ℝ) (hα : 0 ≤ α) (C : Matrix (Fin mF) (Fin mF) ℝ)
    (hC : C.transpose = C) (c : ℝ) :
    Integrable (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ => (rowOf 0 F₃ ⬝ᵥ C *ᵥ rowOf 0 F₃ - c) ^ 2)
      (gaussMat 1 mF α) ∧
    ∫ F₃, (rowOf 0 F₃ ⬝ᵥ C *ᵥ rowOf 0 F₃ - c) ^ 2 ∂gaussMat 1 mF α =
      (α * C.trace - c) ^ 2 + 2 * α ^ 2 * ∑ i, ∑ j, C i j ^ 2 := by
  have hc : Continuous fun w : Fin mF → ℝ => (w ⬝ᵥ C *ᵥ w - c) ^ 2 := by fun_prop
  have hq : ∀ ξ : Fin mF → ℝ, (√α • ξ) ⬝ᵥ C *ᵥ (√α • ξ) = α * (ξ ⬝ᵥ C *ᵥ ξ) := by
    intro ξ
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← mul_assoc, Real.mul_self_sqrt hα]
  obtain ⟨i2, e2⟩ := qform_sq_integral C hC
  have i1 := qform_integrable C
  have e1 := qform_integral C
  have hexp : ∀ ξ : Fin mF → ℝ, (α * (ξ ⬝ᵥ C *ᵥ ξ) - c) ^ 2 =
      α ^ 2 * (ξ ⬝ᵥ C *ᵥ ξ) ^ 2 - 2 * α * c * (ξ ⬝ᵥ C *ᵥ ξ) + c ^ 2 := fun ξ => by ring
  have iA : Integrable (fun ξ : Fin mF → ℝ => α ^ 2 * (ξ ⬝ᵥ C *ᵥ ξ) ^ 2 -
      2 * α * c * (ξ ⬝ᵥ C *ᵥ ξ)) (stdGauss (Fin mF)) :=
    (i2.const_mul _).sub (i1.const_mul _)
  have iS : Integrable (fun ξ : Fin mF → ℝ => (α * (ξ ⬝ᵥ C *ᵥ ξ) - c) ^ 2)
      (stdGauss (Fin mF)) := by
    simp_rw [hexp]
    exact iA.add (integrable_const _)
  constructor
  · have h1 : Integrable (fun w : Fin mF → ℝ => (w ⬝ᵥ C *ᵥ w - c) ^ 2)
        ((gaussMat 1 mF α).map (rowOf 0)) := by
      rw [gaussMat_row, integrable_map_measure hc.measurable.aestronglyMeasurable
        (measurable_const_smul _).aemeasurable]
      simp only [Function.comp_def, hq]
      exact iS
    exact (integrable_map_measure hc.measurable.aestronglyMeasurable
      (measurable_rowOf 0).aemeasurable).mp h1
  · rw [← integral_map (measurable_rowOf 0).aemeasurable hc.measurable.aestronglyMeasurable
        (f := fun w : Fin mF → ℝ => (w ⬝ᵥ C *ᵥ w - c) ^ 2),
      gaussMat_row, integral_map (measurable_const_smul _).aemeasurable
        hc.measurable.aestronglyMeasurable]
    simp only [hq, hexp]
    rw [integral_add iA (integrable_const _), integral_sub (i2.const_mul _) (i1.const_mul _),
      integral_const_mul, integral_const_mul, e1, e2]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring

/-! ## The trace and the Frobenius norm of the covariance, in terms of the kernel -/

/-- The mean over `(u, u′)` of the diagonal kernel `k(u, u)`. -/
noncomputable def VS (r : Rest N mW n mA mF) : ℝ := ∫ uu, kgen false false true (uu, r) ∂lawU2 N

/-- The mean over `(u, u′)` of the kernel `k(u, u′)` (the same Agent network at both inputs). -/
noncomputable def PS (r : Rest N mW n mA mF) : ℝ := ∫ uu, kgen false false false (uu, r) ∂lawU2 N

/-- The mean over `(u, u′)` of `(k(u, u′) − c)²`. -/
noncomputable def QS (c : ℝ) (r : Rest N mW n mA mF) : ℝ :=
  ∫ uu, (kgen false false false (uu, r) - c) ^ 2 ∂lawU2 N

/-- The last hidden vector of `F` at `A(x(u))`, as a function of the input `u`. -/
noncomputable def zU (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ) (u : Fin N → ℝ) :
    Fin mF → ℝ :=
  hidF F₁ F₂ A (xW W u)

section fixed

variable (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N mW n) (A : MlpParam n mA n)
  (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)

lemma zU_meas (i : Fin mF) : Measurable fun u => zU W A F₁ F₂ u i :=
  (continuous_hidF F₁ F₂ A i).measurable.comp (measurable_sphPt_mlpEval W)

include hn in
lemma zU_bdd : ∃ B : ℝ, ∀ u i, |zU W A F₁ F₂ u i| ≤ B := by
  have hc : Continuous fun x : Fin n → ℝ => ∑ i, |hidF F₁ F₂ A x i| :=
    continuous_finsetSum _ fun i _ => (continuous_hidF F₁ F₂ A i).abs
  obtain ⟨C, hC⟩ := isCompact_unit.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun u i => ?_⟩
  have h1 := hC (xW W u) (normSq_xW hn W u)
  have h2 : |hidF F₁ F₂ A (xW W u) i| ≤ ∑ i, |hidF F₁ F₂ A (xW W u) i| :=
    Finset.single_le_sum (f := fun i => |hidF F₁ F₂ A (xW W u) i|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  exact h2.trans ((le_abs_self _).trans h1)

lemma aVec_eq (i : Fin mF) :
    aVec W A F₁ F₂ i = meanV (uniformSphere N) (zU W A F₁ F₂) i := by
  unfold aVec meanV muWn
  exact integral_map (measurable_sphPt_mlpEval W).aemeasurable
    (continuous_hidF F₁ F₂ A i).measurable.aestronglyMeasurable

lemma covMat_eq (i j : Fin mF) :
    covMat W A F₁ F₂ i j = covV (uniformSphere N) (zU W A F₁ F₂) i j := by
  simp only [covMat, of_apply, covV, ← aVec_eq]
  unfold muWn
  exact integral_map (measurable_sphPt_mlpEval W).aemeasurable
    (((continuous_hidF F₁ F₂ A i).sub continuous_const).mul
      ((continuous_hidF F₁ F₂ A j).sub continuous_const)).measurable.aestronglyMeasurable

end fixed

lemma kgen_fff (uu : (Fin N → ℝ) × (Fin N → ℝ)) (r : Rest N mW n mA mF) :
    kgen false false false (uu, r) =
      2 / (mF : ℝ) * ∑ i, zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 uu.1 i *
        zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 uu.2 i := rfl

lemma kgen_fft (uu : (Fin N → ℝ) × (Fin N → ℝ)) (r : Rest N mW n mA mF) :
    kgen false false true (uu, r) =
      2 / (mF : ℝ) * ∑ i, zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 uu.1 i *
        zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 uu.1 i := rfl

/-- `α·tr Σ_A = E_u k(u, u) − E_{u,u′} k(u, u′)`. -/
lemma tr_eq (hn : 1 ≤ n) (hN : 1 ≤ N) (r : Rest N mW n mA mF) :
    2 / (mF : ℝ) * (covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1).trace = VS r - PS r := by
  have := uniformSphere_isProbability N hN
  have h := covV_trace (uniformSphere N) (zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1)
    (zU_meas _ _ _ _) (zU_bdd hn _ _ _ _)
  have e1 : (covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1).trace =
      ∑ i, covV (uniformSphere N) (zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1) i i := by
    simp only [Matrix.trace, Matrix.diag, covMat_eq]
  rw [e1, h]
  unfold VS PS lawU2
  simp_rw [kgen_fff, kgen_fft]
  rw [integral_const_mul, integral_const_mul,
    integral_fun_fst (μ := uniformSphere N) (ν := uniformSphere N)
      (f := fun u => ∑ i, zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 u i *
        zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 u i)]
  simp only [probReal_univ, one_smul]
  have e2 : ∀ u : Fin N → ℝ, ∑ i, zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 u i ^ 2 =
      ∑ i, zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 u i * zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 u i :=
    fun u => Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e2]
  ring

/-- `α²·Σ_{ij} (Σ_A)_{ij}² ≤ E_{u,u′}(k(u, u′) − c)²` for every constant `c`. -/
lemma frob_le (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) (r : Rest N mW n mA mF) (c : ℝ) :
    (2 / (mF : ℝ)) ^ 2 * ∑ i, ∑ j, covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 i j ^ 2 ≤ QS c r := by
  have := uniformSphere_isProbability N hN
  have hm : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hα : (2 : ℝ) / mF ≠ 0 := by positivity
  have h := covV_frob_le (uniformSphere N) (zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1)
    (zU_meas _ _ _ _) (zU_bdd hn _ _ _ _) (c / (2 / (mF : ℝ)))
  simp_rw [covMat_eq]
  have h2 := mul_le_mul_of_nonneg_left h (sq_nonneg (2 / (mF : ℝ)))
  refine h2.trans (le_of_eq ?_)
  unfold QS lawU2
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun uu => ?_)
  change _ = (kgen false false false (uu, r) - c) ^ 2
  rw [kgen_fff]
  field_simp

/-- **The second moment of the realized spread over the last matrix of `F`.** For fixed
`(W, A, F₁, F₂)` and constants `c`, `c₁`:
`E_{F₃}(sd² − c)² ≤ (VS − PS − c)² + 2·E_{u,u′}(k − c₁)²`. -/
lemma cond_sq (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) (r : Rest N mW n mA mF) (c c₁ : ℝ) :
    Integrable (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ =>
      (sdn r.1 r.2.1 (r.2.2.2.1, r.2.2.2.2.1, F₃) ^ 2 - c) ^ 2) (gaussMat 1 mF (2 / (mF : ℝ))) ∧
    ∫ F₃, (sdn r.1 r.2.1 (r.2.2.2.1, r.2.2.2.2.1, F₃) ^ 2 - c) ^ 2 ∂gaussMat 1 mF (2 / (mF : ℝ)) ≤
      (VS r - PS r - c) ^ 2 + 2 * QS c₁ r := by
  have e : (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ =>
      (sdn r.1 r.2.1 (r.2.2.2.1, r.2.2.2.2.1, F₃) ^ 2 - c) ^ 2) =
      fun F₃ => (rowOf 0 F₃ ⬝ᵥ covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 *ᵥ rowOf 0 F₃ - c) ^ 2 := by
    funext F₃
    rw [sdn_last hn hN, Real.sq_sqrt (covMat_nonneg hn hN _ _ _ _ _)]
  obtain ⟨hi, he⟩ := gaussRow_qform_sq (2 / (mF : ℝ)) (by positivity)
    (covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1) (covMat_symm _ _ _ _) c
  rw [e]
  refine ⟨hi, ?_⟩
  rw [he, tr_eq hn hN r]
  have := frob_le hn hN hmF r c₁
  nlinarith

/-! ## The mean over the networks -/

lemma lintegral_prod_mono' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {f g : α × β → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ x, ∫⁻ y, f (x, y) ∂ν ≤ ∫⁻ y, g (x, y) ∂ν) :
    ∫⁻ z, f z ∂(μ.prod ν) ≤ ∫⁻ z, g z ∂(μ.prod ν) := by
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ hg.aemeasurable]
  exact lintegral_mono h

lemma measurable_sdn_R (hN : 1 ≤ N) :
    Measurable (fun r : Rest N mW n mA mF => sdn r.1 r.2.1 r.2.2.2) := by
  have h : Measurable (fun r : Rest N mW n mA mF => (r.1, r.2.1, r.2.2.2)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have h3 := (measurable_sdn (mW := mW) (mA := mA) (mF := mF) hN).comp h
  simp only [Function.comp_def] at h3
  exact h3

/-- **The second moment of the realized spread around `c_D − c_P`.** If
`‖k − c_P‖₂ ≤ e_P` and `‖k_diag − c_D‖₂ ≤ e_D` (the two kernels of Part 132 under
`(u, u′) ⊗ (W, A, A′, F)`), then `E(sd² − (c_D − c_P))² ≤ (e_D + e_P)² + 2·e_P²`. -/
theorem spread_L2 (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) {eP eD cP cD : ℝ} (hP : 0 ≤ eP)
    (hD : 0 ≤ eD)
    (hSame : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false false false ω - cP) eP)
    (hDiag : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false false true ω - cD) eD) :
    ∫⁻ r : Rest N mW n mA mF,
        ENNReal.ofReal ((sdn r.1 r.2.1 r.2.2.2 ^ 2 - (cD - cP)) ^ 2) ∂lawR N mW n mA mF ≤
      ENNReal.ofReal ((eD + eP) ^ 2 + 2 * eP ^ 2) := by
  have := lawU2_prob hN
  set f : Rest N mW n mA mF → ℝ≥0∞ :=
    fun r => ENNReal.ofReal ((sdn r.1 r.2.1 r.2.2.2 ^ 2 - (cD - cP)) ^ 2) with hf
  set Rr : Rest N mW n mA mF → ℝ :=
    fun r => (VS r - PS r - (cD - cP)) ^ 2 + 2 * QS cP r with hRr
  set g : Rest N mW n mA mF → ℝ≥0∞ := fun r => ENNReal.ofReal (Rr r) with hg
  have mf : Measurable f :=
    ENNReal.measurable_ofReal.comp ((((measurable_sdn_R hN).pow_const 2).sub
      measurable_const).pow_const 2)
  have mVS : Measurable (VS (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)) :=
    (measurable_kgen false false true).stronglyMeasurable.integral_prod_left'.measurable
  have mPS : Measurable (PS (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)) :=
    (measurable_kgen false false false).stronglyMeasurable.integral_prod_left'.measurable
  have mQS : Measurable (QS (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) cP) :=
    (((measurable_kgen false false false).sub
      measurable_const).pow_const 2).stronglyMeasurable.integral_prod_left'.measurable
  have mRr : Measurable Rr :=
    (((mVS.sub mPS).sub measurable_const).pow_const 2).add (mQS.const_mul 2)
  have mg : Measurable g := ENNReal.measurable_ofReal.comp mRr
  -- the conditional step, and the Fubini steps
  have h5 : ∀ (W : MlpParam N mW n) (A A' : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ)
      (F₂ : Matrix (Fin mF) (Fin mF) ℝ),
      ∫⁻ F₃, f (W, A, A', F₁, F₂, F₃) ∂gaussMat 1 mF (2 / (mF : ℝ)) ≤
        ∫⁻ F₃, g (W, A, A', F₁, F₂, F₃) ∂gaussMat 1 mF (2 / (mF : ℝ)) := by
    intro W A A' F₁ F₂
    have hconst : ∀ F₃ : Matrix (Fin 1) (Fin mF) ℝ,
        g (W, A, A', F₁, F₂, F₃) = g (W, A, A', F₁, F₂, 0) := fun _ => rfl
    simp_rw [hconst]
    rw [lintegral_const, measure_univ, mul_one]
    obtain ⟨hi, hle⟩ := cond_sq hn hN hmF
      ((W, A, A', F₁, F₂, 0) : Rest N mW n mA mF) (cD - cP) cP
    have e : ∫⁻ F₃, f (W, A, A', F₁, F₂, F₃) ∂gaussMat 1 mF (2 / (mF : ℝ)) =
        ENNReal.ofReal (∫ F₃, (sdn W A (F₁, F₂, F₃) ^ 2 - (cD - cP)) ^ 2
          ∂gaussMat 1 mF (2 / (mF : ℝ))) :=
      (ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    rw [e]
    exact ENNReal.ofReal_le_ofReal hle
  have h4 : ∀ (W : MlpParam N mW n) (A A' : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ),
      ∫⁻ y, f (W, A, A', F₁, y)
          ∂((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))) ≤
        ∫⁻ y, g (W, A, A', F₁, y)
          ∂((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))) :=
    fun W A A' F₁ => lintegral_prod_mono'
      (f := fun y => f (W, A, A', F₁, y)) (g := fun y => g (W, A, A', F₁, y))
      (mf.comp (by fun_prop)) (mg.comp (by fun_prop)) (fun F₂ => h5 W A A' F₁ F₂)
  have h3 : ∀ (W : MlpParam N mW n) (A A' : MlpParam n mA n),
      ∫⁻ y, f (W, A, A', y) ∂mlpGauss n mF 1 ≤ ∫⁻ y, g (W, A, A', y) ∂mlpGauss n mF 1 :=
    fun W A A' => lintegral_prod_mono'
      (f := fun y => f (W, A, A', y)) (g := fun y => g (W, A, A', y))
      (mf.comp (by fun_prop)) (mg.comp (by fun_prop)) (fun F₁ => h4 W A A' F₁)
  have h2 : ∀ (W : MlpParam N mW n) (A : MlpParam n mA n),
      ∫⁻ y, f (W, A, y) ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) ≤
        ∫⁻ y, g (W, A, y) ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) :=
    fun W A => lintegral_prod_mono'
      (f := fun y => f (W, A, y)) (g := fun y => g (W, A, y))
      (mf.comp (by fun_prop)) (mg.comp (by fun_prop)) (fun A' => h3 W A A')
  have h1 : ∀ W : MlpParam N mW n,
      ∫⁻ y, f (W, y) ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) ≤
        ∫⁻ y, g (W, y) ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) :=
    fun W => lintegral_prod_mono'
      (f := fun y => f (W, y)) (g := fun y => g (W, y))
      (mf.comp (by fun_prop)) (mg.comp (by fun_prop)) (fun A => h2 W A)
  have h0 : ∫⁻ r, f r ∂lawR N mW n mA mF ≤ ∫⁻ r, g r ∂lawR N mW n mA mF :=
    lintegral_prod_mono' mf mg h1
  refine h0.trans ?_
  -- the mean of the bound
  have sD := section_L2 hn hN false false true hDiag
  have sP := section_L2 hn hN false false false hSame
  have sX := sD.add0 sP.neg hD hP
  have iX : Integrable (fun r : Rest N mW n mA mF => (VS r - PS r - (cD - cP)) ^ 2)
      (lawR N mW n mA mF) := by
    refine sX.int_sq.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [VS, PS]
    ring
  have eX : ∫ r : Rest N mW n mA mF, (VS r - PS r - (cD - cP)) ^ 2 ∂lawR N mW n mA mF ≤
      (eD + eP) ^ 2 := by
    refine le_trans (le_of_eq ?_) sX.le
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [VS, PS]
    ring
  have iQ : Integrable (QS (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) cP)
      (lawR N mW n mA mF) := hSame.int_sq.integral_prod_right
  have eQ : ∫ r, QS cP r ∂lawR N mW n mA mF ≤ eP ^ 2 := by
    have := integral_prod_symm (μ := lawU2 N) (ν := lawR N mW n mA mF) _ hSame.int_sq
    unfold QS
    rw [← this]
    exact hSame.le
  have iR : Integrable Rr (lawR N mW n mA mF) := iX.add (iQ.const_mul 2)
  have hR0 : ∀ r, 0 ≤ Rr r := fun r => by
    have : 0 ≤ QS cP r := integral_nonneg fun _ => sq_nonneg _
    rw [hRr]
    positivity
  rw [hg, ← ofReal_integral_eq_lintegral_ofReal iR (Filter.Eventually.of_forall hR0)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hRr, integral_add iX (iQ.const_mul 2), integral_const_mul]
  linarith

/-! ## From the four networks to the three networks, and Chebyshev's inequality -/

section drop

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  (μ : Measure α) (ν : Measure β) (τ : Measure γ) [SFinite μ] [IsProbabilityMeasure ν]
  [SFinite τ]

/-- `(w, (a, (a′, f))) ↦ (w, (a′, f))` maps `μ ⊗ (ν ⊗ τ)`-type products to products: the
middle coordinate of a probability measure is dropped. -/
lemma map_dropMid :
    (μ.prod (ν.prod τ)).map (fun p : α × β × γ => (p.1, p.2.2)) = μ.prod τ := by
  have h := Measure.map_prod_map μ (ν.prod τ) (f := id) (g := Prod.snd) measurable_id
    measurable_snd
  rw [Measure.map_id, Measure.map_snd_prod, measure_univ, one_smul] at h
  rw [h]
  rfl

end drop

/-- The distribution of `(W, (A, F))` is the image of `lawR` under
`(W, (A, (A′, F))) ↦ (W, (A, F))`. -/
lemma lawR_drop :
    (lawR N mW n mA mF).map (fun r : Rest N mW n mA mF => (r.1, r.2.1, r.2.2.2)) =
      (mlpGauss N mW n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)) := by
  unfold lawR
  have h1 := map_dropMid (mlpGauss n mA n) (mlpGauss n mA n) (mlpGauss n mF 1)
  have h2 := Measure.map_prod_map (mlpGauss N mW n)
    ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) (f := id)
    (g := fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 => (p.1, p.2.2))
    measurable_id (by fun_prop)
  rw [Measure.map_id, h1] at h2
  rw [h2]
  rfl

/-- **Chebyshev's inequality for the realized spread, all widths.** With the hypotheses of
`spread_L2`, `y = c_D − c_P > 0` and `θ < 1`:
`Pr_{W,A,F}(sd² < θ·y) ≤ ((e_D + e_P)² + 2e_P²)/((1 − θ)·y)²`. -/
theorem spreadLow_general (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) {eP eD cP cD : ℝ}
    (hP : 0 ≤ eP) (hD : 0 ≤ eD)
    (hSame : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false false false ω - cP) eP)
    (hDiag : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false false true ω - cD) eD)
    (hy : 0 < cD - cP) {θ : ℝ} (hθ : θ < 1) :
    ((mlpGauss N mW n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))).real
        {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (cD - cP)} ≤
      ((eD + eP) ^ 2 + 2 * eP ^ 2) / ((1 - θ) * (cD - cP)) ^ 2 := by
  set T := (mlpGauss N mW n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)) with hT
  set y := cD - cP with hyd
  have hgap : 0 < (1 - θ) * y := mul_pos (by linarith) hy
  have hgap2 : 0 < ((1 - θ) * y) ^ 2 := by positivity
  set F : MlpParam N mW n × MlpParam n mA n × MlpParam n mF 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - y) ^ 2) with hF
  have mF' : Measurable F :=
    ENNReal.measurable_ofReal.comp ((((measurable_sdn (mA := mA) (mF := mF) hN).pow_const 2).sub
      measurable_const).pow_const 2)
  have mπ : Measurable (fun r : Rest N mW n mA mF => (r.1, r.2.1, r.2.2.2)) := by fun_prop
  have hL : ∫⁻ t, F t ∂T ≤ ENNReal.ofReal ((eD + eP) ^ 2 + 2 * eP ^ 2) := by
    rw [hT, ← lawR_drop, lintegral_map mF' mπ]
    exact spread_L2 hn hN hmF hP hD hSame hDiag
  have hsub : {t : MlpParam N mW n × MlpParam n mA n × MlpParam n mF 1 |
      sdn t.1 t.2.1 t.2.2 ^ 2 < θ * y} ⊆ {t | ENNReal.ofReal (((1 - θ) * y) ^ 2) ≤ F t} := by
    intro t ht
    have ht' : sdn t.1 t.2.1 t.2.2 ^ 2 < θ * y := ht
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  have hmark := mul_meas_ge_le_lintegral (μ := T) mF' (ENNReal.ofReal (((1 - θ) * y) ^ 2))
  have h1 : ENNReal.ofReal (((1 - θ) * y) ^ 2) * T {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * y} ≤
      ENNReal.ofReal ((eD + eP) ^ 2 + 2 * eP ^ 2) :=
    (mul_le_mul' le_rfl (measure_mono hsub)).trans (hmark.trans hL)
  have hv : (0 : ℝ) ≤ (eD + eP) ^ 2 + 2 * eP ^ 2 := by positivity
  rw [le_div_iff₀ hgap2, mul_comm]
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hgap2.le, ENNReal.toReal_ofReal hv] at h2
  exact h2

end general

/-! ## The widths of the Focus -/

/-- The constant `e_P` of Part 133 at the widths of the Focus: `‖k − S·Q‖₂ ≤ S·e_P`. -/
noncomputable def eP139 (n : ℕ) : ℝ :=
  eAFr n (mA n) (mF n) + eWr (2 * n) n (mW n) + sU (2 * n)

/-- `v_n = (e_V + e_P)² + 2·e_P²`: the bound of `E(sd² − S(1 − Q))²/S²`. -/
noncomputable def vSpread (n : ℕ) : ℝ :=
  (eV n (mA n) (mF n) + eP139 n) ^ 2 + 2 * eP139 n ^ 2

/-- **Item 2 (`spreadLow139`).** For `n ≥ 4096` and `θ < 1`, with `S = 4/n`, `Q = κ^{∘6}(0)`:
`Pr_{W,A,F}(sd² < θ·S·(1 − Q)) ≤ ((e_V + e_P)² + 2e_P²)/((1 − θ)(1 − Q))²`. -/
theorem spreadLow139 {n : ℕ} (hn : 4096 ≤ n) {θ : ℝ} (hθ : θ < 1) :
    (mlpTriple 2 n).real
        {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (1 - kappa^[6] 0))} ≤
      vSpread n / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hmW : 1 ≤ mW n := by have := mW_ge hn; omega
  have hd : dChi n ≤ 1 := (dChi_bound hn).trans (by norm_num)
  obtain ⟨hSame, -, hDiag⟩ := kernels_general (N := 2 * n) hn1 hN hmW hmA hmF hd
  obtain ⟨hP0, -, hV0, -⟩ := vTot_nonneg (2 * n) (mW n) n (mA n) (mF n) hmF hmA hn1
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hS : (0 : ℝ) < 4 / (n : ℝ) := by positivity
  have hy : 0 < 4 / (n : ℝ) - 4 / (n : ℝ) * kappa^[6] 0 := by nlinarith
  have h := spreadLow_general hn1 hN hmF (mul_nonneg hS.le hP0) (mul_nonneg hS.le hV0)
    hSame hDiag hy hθ
  have e1 : 4 / (n : ℝ) - 4 / (n : ℝ) * kappa^[6] 0 = 4 / (n : ℝ) * (1 - kappa^[6] 0) := by ring
  rw [e1] at h
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  rw [e0]
  refine h.trans (le_of_eq ?_)
  have h1Q : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  unfold vSpread eP139
  field_simp

/-- `e_P ≤ 0.06369` and `e_V ≤ 0.023` for `n ≥ 4096`; so `v_n ≤ 0.01563`. -/
lemma vSpread_le {n : ℕ} (hn : 4096 ≤ n) : vSpread n ≤ 1563 / 100000 := by
  have hn1 : 1 ≤ n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  obtain ⟨hP0, -, hV0, -⟩ := vTot_nonneg (2 * n) (mW n) n (mA n) (mF n) hmF hmA hn1
  have h1 := eAFr_bound hn
  have h2 := eWr_bound hn
  have h3 := sU_bound hn
  have h4 := eV_bound hn
  have hP : eP139 n ≤ 6369 / 100000 := by unfold eP139; linarith
  have hP0' : 0 ≤ eP139 n := hP0
  unfold vSpread
  nlinarith

/-- **Item 2 with explicit constants.** For `n ≥ 4096` and `0 ≤ θ < 1`:
`Pr_{W,A,F}(sd² < θ·S·(1 − Q)) ≤ 0.01563/((1 − θ)·0.222)²`. -/
theorem spreadLow139_num {n : ℕ} (hn : 4096 ≤ n) {θ : ℝ} (hθ : θ < 1) :
    (mlpTriple 2 n).real
        {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (1 - kappa^[6] 0))} ≤
      1563 / 100000 / ((1 - θ) * (222 / 1000)) ^ 2 := by
  have h := spreadLow139 hn hθ
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hv := vSpread_le hn
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hv0 : 0 ≤ vSpread n := by unfold vSpread; positivity
  refine h.trans ?_
  have hden : ((1 - θ) * (222 / 1000)) ^ 2 ≤ ((1 - θ) * (1 - kappa^[6] 0)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) h1θ.le
  calc vSpread n / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2
      ≤ vSpread n / ((1 - θ) * (222 / 1000)) ^ 2 :=
        div_le_div_of_nonneg_left hv0 (by positivity) hden
    _ ≤ _ := div_le_div_of_nonneg_right hv (by positivity)

end BstLean.Part139

open BstLean.Part139 in
#print axioms gaussRow_qform_sq
open BstLean.Part139 in
#print axioms cond_sq
open BstLean.Part139 in
#print axioms spread_L2
open BstLean.Part139 in
#print axioms spreadLow_general
open BstLean.Part139 in
#print axioms spreadLow139
open BstLean.Part139 in
#print axioms spreadLow139_num
