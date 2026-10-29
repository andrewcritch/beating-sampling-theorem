import BstLean.Part154MFv
import BstLean.Part154MFbias
import BstLean.Part154PR
import BstLean.Part154K0
import BstLean.Part153Bin

/-!
# Part 154: Lemma MF (the mean-field lemma)
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (relu reluV normSq)
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm)
open BstLean.Part131 (projMat projMat_mulVec stdGauss_decomp)
open Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {f : Ω → Fin m → ℝ} {ℓ πg : ℝ}

/-- The unit vector `f̄/|f̄|`. -/
noncomputable def eF (μ : Measure Ω) (f : Ω → Fin m → ℝ) : Fin m → ℝ :=
  (nrm (fbar μ f))⁻¹ • fbar μ f

/-! ## Auxiliary facts -/

lemma dot_self_normSq (v : Fin m → ℝ) : v ⬝ᵥ v = normSq v := by
  simp [dotProduct, normSq, sq]

lemma meas_dotT {α : Type*} [MeasurableSpace α] {u v : α → Fin m → ℝ} (hu : Measurable u)
    (hv : Measurable v) : Measurable (fun x => u x ⬝ᵥ v x) := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hu).mul ((measurable_pi_apply i).comp hv)

lemma abs_dot_le (z v : Fin m → ℝ) : |z ⬝ᵥ v| ≤ (normSq z + normSq v) / 2 := by
  simp only [dotProduct, normSq]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (z i - v i), sq_nonneg (z i + v i)]

omit [IsProbabilityMeasure μ] in
theorem MFHyp.nrm_pos (H : MFHyp μ f ℓ πg) : 0 < nrm (fbar μ f) := Real.sqrt_pos.mpr H.hbar

omit [IsProbabilityMeasure μ] in
theorem MFHyp.eF_unit (H : MFHyp μ f ℓ πg) : eF μ f ⬝ᵥ eF μ f = 1 := by
  have hp := H.nrm_pos
  have h2 : nrm (fbar μ f) ^ 2 = normSq (fbar μ f) := BstLean.Part153.nrm_sq _
  unfold eF
  rw [smul_dotProduct, dotProduct_smul, dot_self_normSq, ← h2]
  simp only [smul_eq_mul]
  field_simp

omit [IsProbabilityMeasure μ] in
theorem MFHyp.fbar_eq (H : MFHyp μ f ℓ πg) : fbar μ f = nrm (fbar μ f) • eF μ f := by
  unfold eF
  rw [smul_smul, mul_inv_cancel₀ H.nrm_pos.ne', one_smul]

omit [IsProbabilityMeasure μ] in
theorem MFHyp.decomp_dot_fbar (H : MFHyp μ f ℓ πg) (ζ : ℝ) (z' : Fin m → ℝ) :
    (ζ • eF μ f + (projMat (eF μ f)).mulVec z') ⬝ᵥ fbar μ f = ζ * nrm (fbar μ f) := by
  have he := H.eF_unit
  have h0 := BstLean.Part131.projMat_dot he z'
  have hf : (ζ • eF μ f + (projMat (eF μ f)).mulVec z') ⬝ᵥ fbar μ f =
      (ζ • eF μ f + (projMat (eF μ f)).mulVec z') ⬝ᵥ (nrm (fbar μ f) • eF μ f) := by
    rw [← H.fbar_eq]
  rw [hf, dotProduct_smul, add_dotProduct, smul_dotProduct, he, h0]
  simp only [smul_eq_mul]
  ring

theorem MFHyp.decomp_dot_g (H : MFHyp μ f ℓ πg) (ζ : ℝ) (z' : Fin m → ℝ) (ω : Ω) :
    (ζ • eF μ f + (projMat (eF μ f)).mulVec z') ⬝ᵥ gF μ f ω = z' ⬝ᵥ gF μ f ω := by
  have hg : eF μ f ⬝ᵥ gF μ f ω = 0 := by
    unfold eF
    rw [smul_dotProduct, dotProduct_comm, H.g_dot_fbar]
    simp
  rw [projMat_mulVec, add_dotProduct, sub_dotProduct, smul_dotProduct, smul_dotProduct, hg]
  simp

lemma meas_phi (e : Fin m → ℝ) :
    Measurable (fun p : ℝ × (Fin m → ℝ) => p.1 • e + (projMat e).mulVec p.2) := by
  simp only [projMat_mulVec]
  exact (measurable_fst.smul_const e).add
    (measurable_snd.sub ((meas_dotT measurable_const measurable_snd).smul_const e))

omit [IsProbabilityMeasure μ] in
theorem MFHyp.int_decomp_aux (H : MFHyp μ f ℓ πg) {G : (Fin m → ℝ) → ℝ} (hG : Measurable G)
    (hGi : Integrable G (stdGauss (Fin m))) :
    Integrable (fun p : ℝ × (Fin m → ℝ) => G (p.1 • eF μ f + (projMat (eF μ f)).mulVec p.2))
      ((gaussianReal 0 1).prod (stdGauss (Fin m))) := by
  have hd := stdGauss_decomp (H.eF_unit)
  have hGi' : Integrable G (((gaussianReal 0 1).prod (stdGauss (Fin m))).map
      (fun p => p.1 • eF μ f + (projMat (eF μ f)).mulVec p.2)) := by rw [hd]; exact hGi
  exact (integrable_map_measure hG.aestronglyMeasurable (meas_phi _).aemeasurable).mp hGi'

/-- The inner integral is a measurable function of `ζ`. -/
lemma meas_inner (e : Fin m → ℝ) {G : (Fin m → ℝ) → ℝ} (hG : Measurable G) :
    Measurable (fun ζ : ℝ => ∫ z', G (ζ • e + (projMat e).mulVec z') ∂stdGauss (Fin m)) :=
  (hG.comp (meas_phi e)).stronglyMeasurable.integral_prod_right'.measurable

/-! ## Moments of a standard Gaussian number -/

/-- `E|Z|³ = 2√(2/π)`. -/
theorem gauss_abs3 : ∫ z, |z| ^ 3 ∂gaussianReal 0 1 = 2 * √(2 / π) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have e : ∀ x : ℝ, gaussianPDFReal 0 1 x • |x| ^ 3 =
      (fun y : ℝ => (√(2 * π))⁻¹ * (y ^ 3 * rexp (-(y ^ 2 / 2)))) |x| := by
    intro x
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero, sq_abs]
    rw [show -x ^ 2 / 2 = -(x ^ 2 / 2) by ring]; ring
  simp_rw [e]
  refine Eq.trans (integral_comp_abs (f := fun y : ℝ => (√(2 * π))⁻¹ * (y ^ 3 * rexp (-(y ^ 2 / 2))))) ?_
  have hd : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt (fun t : ℝ => -((t ^ 2 + 2) * rexp (-(t ^ 2 / 2))))
      (x ^ 3 * rexp (-(x ^ 2 / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2 / 2)) (-x) x := by
      have := ((hasDerivAt_pow 2 x).div_const 2).neg
      convert this using 1; ring
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 + 2) (2 * x) x := by
      have := (hasDerivAt_pow 2 x).add_const 2
      convert this using 1; ring
    have h := (h2.mul h1.exp).neg
    convert h using 1; ring
  have ht : Tendsto (fun t : ℝ => -((t ^ 2 + 2) * rexp (-(t ^ 2 / 2)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).atTop_div_const (by norm_num)
    have ha := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h1
    have hb := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have hc := ((ha.const_mul 2).add (hb.const_mul 2)).neg
    simp only [mul_zero, add_zero, neg_zero] at hc
    refine hc.congr fun t => ?_
    simp only [Function.comp, pow_one]
    ring
  have hI : ∫ x in Set.Ioi (0 : ℝ), x ^ 3 * rexp (-(x ^ 2 / 2)) = 2 := by
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun x hx => by
      have : (0 : ℝ) < x := hx
      positivity) ht]
    norm_num
  rw [integral_const_mul, hI]
  have hp : (0 : ℝ) < π := Real.pi_pos
  have h2 : √(2 * π) * √(2 / π) = 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show 2 * π * (2 / π) = 2 ^ 2 by field_simp]
    exact Real.sqrt_sq (by norm_num)
  have h3 : (0 : ℝ) < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  field_simp
  linarith

/-- The Gaussian integral of `(c₀ + c₁|ζ| + c₂ζ²)²`. -/
theorem poly_gauss (c0 c1 c2 : ℝ) :
    Integrable (fun ζ : ℝ => (c0 + c1 * |ζ| + c2 * ζ ^ 2) ^ 2) (gaussianReal 0 1) ∧
    ∫ ζ, (c0 + c1 * |ζ| + c2 * ζ ^ 2) ^ 2 ∂gaussianReal 0 1 =
      c0 ^ 2 + c1 ^ 2 + 3 * c2 ^ 2 + 2 * √(2 / π) * c0 * c1 + 2 * c0 * c2 +
        4 * √(2 / π) * c1 * c2 := by
  have i1 : Integrable (fun ζ : ℝ => |ζ|) (gaussianReal 0 1) := by
    simpa using (BstLean.Part130.integrable_pow_gauss 1).abs
  have i2 : Integrable (fun ζ : ℝ => ζ ^ 2) (gaussianReal 0 1) :=
    BstLean.Part130.integrable_pow_gauss 2
  have i4 : Integrable (fun ζ : ℝ => ζ ^ 4) (gaussianReal 0 1) :=
    BstLean.Part130.integrable_pow_gauss 4
  have i3 : Integrable (fun ζ : ℝ => |ζ| ^ 3) (gaussianReal 0 1) := by
    simpa [abs_pow] using (BstLean.Part130.integrable_pow_gauss 3).abs
  have m2 : ∫ ζ : ℝ, ζ ^ 2 ∂gaussianReal 0 1 = 1 := by
    rw [BstLean.Part29.gaussMom_eq]; norm_num [BstLean.Part29.gaussMom]
  have m4 : ∫ ζ : ℝ, ζ ^ 4 ∂gaussianReal 0 1 = 3 := by
    rw [BstLean.Part29.gaussMom_eq]
    have : Even 4 := by decide
    simp [BstLean.Part29.gaussMom, this, Nat.doubleFactorial]
  have a0 : Integrable (fun _ : ℝ => c0 ^ 2) (gaussianReal 0 1) := integrable_const _
  have b1 : Integrable (fun ζ : ℝ => c1 ^ 2 * ζ ^ 2) (gaussianReal 0 1) := i2.const_mul _
  have b2 : Integrable (fun ζ : ℝ => c2 ^ 2 * ζ ^ 4) (gaussianReal 0 1) := i4.const_mul _
  have b3 : Integrable (fun ζ : ℝ => 2 * c0 * c1 * |ζ|) (gaussianReal 0 1) := i1.const_mul _
  have b4 : Integrable (fun ζ : ℝ => 2 * c0 * c2 * ζ ^ 2) (gaussianReal 0 1) := i2.const_mul _
  have b5 : Integrable (fun ζ : ℝ => 2 * c1 * c2 * |ζ| ^ 3) (gaussianReal 0 1) := i3.const_mul _
  have a1 : Integrable (fun ζ : ℝ => c0 ^ 2 + c1 ^ 2 * ζ ^ 2) (gaussianReal 0 1) := a0.add b1
  have a2 : Integrable (fun ζ : ℝ => c0 ^ 2 + c1 ^ 2 * ζ ^ 2 + c2 ^ 2 * ζ ^ 4)
      (gaussianReal 0 1) := a1.add b2
  have a3 : Integrable (fun ζ : ℝ => c0 ^ 2 + c1 ^ 2 * ζ ^ 2 + c2 ^ 2 * ζ ^ 4 + 2 * c0 * c1 * |ζ|)
      (gaussianReal 0 1) := a2.add b3
  have a4 : Integrable (fun ζ : ℝ => c0 ^ 2 + c1 ^ 2 * ζ ^ 2 + c2 ^ 2 * ζ ^ 4 + 2 * c0 * c1 * |ζ| +
      2 * c0 * c2 * ζ ^ 2) (gaussianReal 0 1) := a3.add b4
  have a5 : Integrable (fun ζ : ℝ => c0 ^ 2 + c1 ^ 2 * ζ ^ 2 + c2 ^ 2 * ζ ^ 4 + 2 * c0 * c1 * |ζ| +
      2 * c0 * c2 * ζ ^ 2 + 2 * c1 * c2 * |ζ| ^ 3) (gaussianReal 0 1) := a4.add b5
  have e : (fun ζ : ℝ => (c0 + c1 * |ζ| + c2 * ζ ^ 2) ^ 2) =
      fun ζ : ℝ => c0 ^ 2 + c1 ^ 2 * ζ ^ 2 + c2 ^ 2 * ζ ^ 4 + 2 * c0 * c1 * |ζ| +
        2 * c0 * c2 * ζ ^ 2 + 2 * c1 * c2 * |ζ| ^ 3 := by
    funext ζ
    have h := sq_abs ζ
    have h3 : |ζ| ^ 3 = |ζ| * ζ ^ 2 := by rw [← h]; ring
    rw [h3]
    linear_combination (c1 ^ 2) * h
  rw [e]
  refine ⟨a5, ?_⟩
  rw [integral_add a4 b5, integral_add a3 b4, integral_add a2 b3, integral_add a1 b2,
    integral_add a0 b1, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const, m2, m4, gauss_abs3,
    BstLean.Part150.gauss_abs]
  simp only [probReal_univ, one_smul]
  ring

/-- `E(Y − c)² = Var Y + (E Y − c)²`. -/
lemma var_shift {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {Y : α → ℝ} (hY : Integrable Y ν)
    (hV : Integrable (fun x => (Y x - ∫ y, Y y ∂ν) ^ 2) ν) (c : ℝ) :
    ∫ x, (Y x - c) ^ 2 ∂ν = ∫ x, (Y x - ∫ y, Y y ∂ν) ^ 2 ∂ν + (∫ y, Y y ∂ν - c) ^ 2 := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ y, Y y ∂ν := ⟨_, rfl⟩
  rw [← hM] at hV ⊢
  have h1 : Integrable (fun x => Y x - M) ν := hY.sub (integrable_const M)
  have h2 : Integrable (fun x => 2 * (M - c) * (Y x - M)) ν := h1.const_mul _
  have h3 : Integrable (fun _ : α => (M - c) ^ 2) ν := integrable_const _
  have h4 : Integrable (fun x => 2 * (M - c) * (Y x - M) + (M - c) ^ 2) ν := h2.add h3
  have e : (fun x => (Y x - c) ^ 2) =
      fun x => (Y x - M) ^ 2 + (2 * (M - c) * (Y x - M) + (M - c) ^ 2) := by
    funext x; ring
  have hc : ∫ _ : α, M ∂ν = M := by simp
  rw [e, integral_add hV h4, integral_add h2 h3, integral_const_mul,
    integral_sub hY (integrable_const M), hc, ← hM]
  simp

lemma continuous_PhiG : Continuous PhiG :=
  continuous_iff_continuousAt.mpr fun v => (BstLean.Part153.hasDerivAt_PhiG v).continuousAt

/-- `0 ≤ ψ_s(x) ≤ |x| + |s|·√(2/π)`. -/
lemma psiS_le_abs (s x : ℝ) : psiS s x ≤ |x| + |s| * √(2 / π) := by
  have i1 : Integrable (fun ζ : ℝ => |ζ|) (gaussianReal 0 1) := by
    simpa using (BstLean.Part130.integrable_pow_gauss 1).abs
  have i2 : Integrable (fun ζ : ℝ => |s| * |ζ|) (gaussianReal 0 1) := i1.const_mul _
  have i3 : Integrable (fun ζ : ℝ => |x| + |s| * |ζ|) (gaussianReal 0 1) :=
    (integrable_const _).add i2
  have h : psiS s x ≤ ∫ ζ : ℝ, |x| + |s| * |ζ| ∂gaussianReal 0 1 := by
    unfold psiS
    refine integral_mono_of_nonneg (ae_of_all _ fun z => BstLean.Part130.relu_nonneg _) i3
      (ae_of_all _ fun z => ?_)
    have h1 := BstLean.Part130.abs_relu_le (x + s * z)
    have h2 := abs_add_le x (s * z)
    rw [abs_mul] at h2
    exact (le_abs_self _).trans (h1.trans h2)
  rw [integral_add (integrable_const _) i2, integral_const_mul, BstLean.Part150.gauss_abs,
    integral_const] at h
  simpa using h

/-! ## Measurability and integrability of `𝖣` -/

theorem MFHyp.meas_XF (H : MFHyp μ f ℓ πg) : Measurable (XF μ f) := by
  have hF : Measurable (fun q : (Fin m → ℝ) × Ω => relu (q.1 ⬝ᵥ f q.2)) :=
    BstLean.Part130.measurable_relu.comp (meas_dotT measurable_fst (H.hf.comp measurable_snd))
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

theorem MFHyp.meas_DF (H : MFHyp μ f ℓ πg) : Measurable (DF μ f) := by
  have h2 : Measurable (fun z : Fin m → ℝ => psiS (sF μ f) (z ⬝ᵥ fbar μ f)) :=
    BstLean.Part137.measurable_psiS.comp
      (measurable_const.prodMk (meas_dotT measurable_id measurable_const))
  exact H.meas_XF.sub h2

theorem MFHyp.XF_bound (H : MFHyp μ f ℓ πg) (z : Fin m → ℝ) :
    0 ≤ XF μ f z ∧ XF μ f z ≤ (normSq z + GamF μ f) / 2 := by
  refine ⟨integral_nonneg fun _ => BstLean.Part130.relu_nonneg _, ?_⟩
  have i1 : Integrable (fun ω => (normSq z + normSq (f ω)) / 2) μ :=
    ((integrable_const _).add H.int_sq).div_const 2
  have h : XF μ f z ≤ ∫ ω, (normSq z + normSq (f ω)) / 2 ∂μ := by
    unfold XF
    refine integral_mono_of_nonneg (ae_of_all _ fun ω => BstLean.Part130.relu_nonneg _) i1
      (ae_of_all _ fun ω => ?_)
    exact (le_abs_self _).trans ((BstLean.Part130.abs_relu_le _).trans (abs_dot_le z (f ω)))
  rw [integral_div, integral_add (integrable_const _) H.int_sq, integral_const] at h
  simpa [GamF] using h

theorem MFHyp.DF_sq_int (H : MFHyp μ f ℓ πg) :
    Integrable (fun z => DF μ f z ^ 2) (stdGauss (Fin m)) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (GamF μ f + GamBarF μ f) / 2 + |sF μ f| * √(2 / π) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    have h1 : 0 ≤ GamF μ f := by
      have h := (H.XF_bound 0).1.trans (H.XF_bound 0).2
      have hz : normSq (0 : Fin m → ℝ) = 0 := by simp [normSq]
      rw [hz] at h
      linarith
    have h2 := H.hbar
    rw [hC]; positivity
  have j4 : Integrable (fun z : Fin m → ℝ => nrm z ^ (2 * 2)) (stdGauss (Fin m)) :=
    (BstLean.Part153.nrm_moment m (P := 2) (by norm_num)).1
  have j2 : Integrable (fun z : Fin m → ℝ => nrm z ^ 2) (stdGauss (Fin m)) :=
    (BstLean.Part153.int_normSq_std m).1
  have j2' : Integrable (fun z : Fin m → ℝ => 2 * C * nrm z ^ 2) (stdGauss (Fin m)) :=
    j2.const_mul _
  have jB : Integrable (fun z : Fin m → ℝ => nrm z ^ (2 * 2) + 2 * C * nrm z ^ 2 + C ^ 2)
      (stdGauss (Fin m)) := (j4.add j2').add (integrable_const _)
  refine jB.mono' (H.meas_DF.pow_const 2).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_mul, BstLean.Part153.nrm_sq]
  have hX := H.XF_bound z
  have hp0 := BstLean.Part137.psiS_nonneg (sF μ f) (z ⬝ᵥ fbar μ f)
  have hp1 := psiS_le_abs (sF μ f) (z ⬝ᵥ fbar μ f)
  have hd := abs_dot_le z (fbar μ f)
  have hn := BstLean.Part130.normSq_nonneg z
  have hG : GamBarF μ f = normSq (fbar μ f) := rfl
  have hD : |DF μ f z| ≤ normSq z + C := by
    unfold DF
    rw [abs_le]
    constructor <;> nlinarith
  have := sq_le_sq' (abs_le.mp hD).1 (abs_le.mp hD).2
  nlinarith


/-- **Step 1 (regression).** `z = ζ·e + Π z′`: `𝖣(z) = Y_{ā}(z′) − ψ_s(ā)`, `ā = ζ|f̄|`. -/
theorem MFHyp.DF_decomp (H : MFHyp μ f ℓ πg) (ζ : ℝ) (z' : Fin m → ℝ) :
    DF μ f (ζ • eF μ f + (BstLean.Part131.projMat (eF μ f)).mulVec z') =
      YF μ f (ζ * nrm (fbar μ f)) z' - psiS (sF μ f) (ζ * nrm (fbar μ f)) := by
  have h1 := H.decomp_dot_fbar ζ z'
  unfold DF XF YF
  rw [h1]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  beta_reduce
  rw [dot_decomp μ f (ζ • eF μ f + (projMat (eF μ f)).mulVec z') ω, h1, H.decomp_dot_g]

/-- The integral of a function of `z` as an iterated integral over `ā` and `z′`. -/
theorem MFHyp.int_decomp (H : MFHyp μ f ℓ πg) {G : (Fin m → ℝ) → ℝ} (hG : Measurable G)
    (hGi : Integrable G (stdGauss (Fin m))) :
    ∫ z, G z ∂stdGauss (Fin m) =
      ∫ ζ, (∫ z', G (ζ • eF μ f + (BstLean.Part131.projMat (eF μ f)).mulVec z') ∂stdGauss (Fin m))
        ∂gaussianReal 0 1 := by
  have hi := H.int_decomp_aux hG hGi
  calc ∫ z, G z ∂stdGauss (Fin m)
      = ∫ z, G z ∂(((gaussianReal 0 1).prod (stdGauss (Fin m))).map
          (fun p => p.1 • eF μ f + (projMat (eF μ f)).mulVec p.2)) := by
        rw [stdGauss_decomp H.eF_unit]
    _ = ∫ p : ℝ × (Fin m → ℝ), G (p.1 • eF μ f + (projMat (eF μ f)).mulVec p.2)
          ∂((gaussianReal 0 1).prod (stdGauss (Fin m))) :=
        integral_map (meas_phi _).aemeasurable hG.aestronglyMeasurable
    _ = _ := integral_prod _ hi

/-! ## The inner integral for a fixed `ζ` -/

theorem MFHyp.inner_mean (H : MFHyp μ f ℓ πg) (ζ : ℝ) :
    ∫ z', DF μ f (ζ • eF μ f + (projMat (eF μ f)).mulVec z') ∂stdGauss (Fin m) =
      (∫ ω, psiS (√(sig2F μ f ω)) (betaF μ f ω * (ζ * nrm (fbar μ f))) ∂μ) -
        psiS (sF μ f) (ζ * nrm (fbar μ f)) := by
  simp_rw [H.DF_decomp]
  have hm := H.YF_mean (ζ * nrm (fbar μ f))
  rw [integral_sub hm.1 (integrable_const _), integral_const, hm.2.2]
  simp

theorem MFHyp.inner_abs_le (H : MFHyp μ f ℓ πg) (ζ : ℝ) :
    |∫ z', DF μ f (ζ • eF μ f + (projMat (eF μ f)).mulVec z') ∂stdGauss (Fin m)| ≤
      sF μ f * (cc0 (ℓ ^ 2 / sF2 μ f) πg + cc1 (ℓ ^ 2 / sF2 μ f) πg * |ζ| +
        cc2 (ℓ ^ 2 / sF2 μ f) * ζ ^ 2) := by
  rw [H.inner_mean]
  have hb := (H.YF_bias (ζ * nrm (fbar μ f))).2
  have hn : nrm (fbar μ f) = √(GamBarF μ f) := rfl
  have hp : 0 < √(GamBarF μ f) := Real.sqrt_pos.mpr H.hbar
  have hsq : √(GamBarF μ f) ^ 2 = GamBarF μ f := Real.sq_sqrt H.hbar.le
  have e1 : |ζ * √(GamBarF μ f)| / √(GamBarF μ f) = |ζ| := by
    rw [abs_mul, abs_of_pos hp]; field_simp
  have e2 : (ζ * √(GamBarF μ f)) ^ 2 / GamBarF μ f = ζ ^ 2 := by
    rw [mul_pow, hsq]; field_simp [H.hbar.ne']
  rw [hn] at hb ⊢
  rw [e1, e2] at hb
  exact hb

theorem MFHyp.inner_sq_le (H : MFHyp μ f ℓ πg) {K : ℝ} (hK0 : 0 ≤ K) (hPR : PRvecBound K)
    (ζ : ℝ) :
    ∫ z', DF μ f (ζ • eF μ f + (projMat (eF μ f)).mulVec z') ^ 2 ∂stdGauss (Fin m) ≤
      ℓ ^ 2 * (∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
          PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ) +
        K * (2 * hsF μ f / sF2 μ f + √2 * sF2 μ f * πg) +
        (sF μ f * (cc0 (ℓ ^ 2 / sF2 μ f) πg + cc1 (ℓ ^ 2 / sF2 μ f) πg * |ζ| +
          cc2 (ℓ ^ 2 / sF2 μ f) * ζ ^ 2)) ^ 2 := by
  have hab := H.inner_abs_le ζ
  have hmean := H.inner_mean ζ
  have hn : nrm (fbar μ f) = √(GamBarF μ f) := rfl
  simp_rw [H.DF_decomp] at hab hmean ⊢
  rw [hn] at hab hmean ⊢
  have hm := H.YF_mean (ζ * √(GamBarF μ f))
  have hV := H.YF_var_le hK0 hPR (ζ * √(GamBarF μ f)) (PhiG (ζ * √(GamBarF μ f) / sF μ f))
  rw [var_shift hm.1 hV.1]
  rw [integral_sub hm.1 (integrable_const _), integral_const] at hab
  simp only [probReal_univ, one_smul] at hab
  have h2 := sq_le_sq' (abs_le.mp hab).1 (abs_le.mp hab).2
  have h3 := hV.2
  linarith

theorem MFHyp.sF_sq (H : MFHyp μ f ℓ πg) : sF μ f ^ 2 = sF2 μ f := H.sF_pos.2

/-- The square of the inner mean is integrable, and its integral is at most `s²·Q_B`. -/
theorem MFHyp.bias_int (H : MFHyp μ f ℓ πg) :
    Integrable (fun ζ : ℝ => (∫ z', DF μ f (ζ • eF μ f + (projMat (eF μ f)).mulVec z')
        ∂stdGauss (Fin m)) ^ 2) (gaussianReal 0 1) := by
  have hp := (poly_gauss (cc0 (ℓ ^ 2 / sF2 μ f) πg) (cc1 (ℓ ^ 2 / sF2 μ f) πg)
    (cc2 (ℓ ^ 2 / sF2 μ f))).1.const_mul (sF2 μ f)
  refine hp.mono' ((meas_inner _ H.meas_DF).pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun ζ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hab := H.inner_abs_le ζ
  have h2 := sq_le_sq' (abs_le.mp hab).1 (abs_le.mp hab).2
  rw [mul_pow, H.sF_sq] at h2
  exact h2


/-- **Lemma MF, the bias** (the first display): `E_z(E[𝖣 | ā])² ≤ s²·Q_B(ϱ, π_g)`. The conditional
expectation given `ā` is the integral over `z′` in the decomposition `z = ζe + Πz′`. -/
theorem MFHyp.lemmaMF_bias (H : MFHyp μ f ℓ πg) :
    ∫ ζ, (∫ z', DF μ f (ζ • eF μ f + (BstLean.Part131.projMat (eF μ f)).mulVec z')
        ∂stdGauss (Fin m)) ^ 2 ∂gaussianReal 0 1 ≤
      sF2 μ f * QB (ℓ ^ 2 / sF2 μ f) πg := by
  have hp := poly_gauss (cc0 (ℓ ^ 2 / sF2 μ f) πg) (cc1 (ℓ ^ 2 / sF2 μ f) πg)
    (cc2 (ℓ ^ 2 / sF2 μ f))
  have h : ∫ ζ, (∫ z', DF μ f (ζ • eF μ f + (projMat (eF μ f)).mulVec z')
        ∂stdGauss (Fin m)) ^ 2 ∂gaussianReal 0 1 ≤
      ∫ ζ, sF2 μ f * (cc0 (ℓ ^ 2 / sF2 μ f) πg + cc1 (ℓ ^ 2 / sF2 μ f) πg * |ζ| +
        cc2 (ℓ ^ 2 / sF2 μ f) * ζ ^ 2) ^ 2 ∂gaussianReal 0 1 := by
    refine integral_mono_of_nonneg (ae_of_all _ fun ζ => sq_nonneg _) (hp.1.const_mul _)
      (ae_of_all _ fun ζ => ?_)
    have hab := H.inner_abs_le ζ
    have h2 := sq_le_sq' (abs_le.mp hab).1 (abs_le.mp hab).2
    rw [mul_pow, H.sF_sq] at h2
    exact h2
  rw [integral_const_mul, hp.2] at h
  unfold QB
  exact h

/-- **Lemma MF** (the second display), with the constant `K` of Lemma PR (i). -/
theorem MFHyp.lemmaMF_K (H : MFHyp μ f ℓ πg) {K : ℝ} (hK : ∀ a, Ures a ≤ K) :
    Integrable (fun z => DF μ f z ^ 2) (stdGauss (Fin m)) ∧
    ∫ z, DF μ f z ^ 2 ∂stdGauss (Fin m) ≤
      2 * K * hsF μ f / sF2 μ f + K * √2 * sF2 μ f * πg +
        ℓ ^ 2 * (1 / π * (2 * (ℓ ^ 2 / sF2 μ f) +
          4 * (√2 - 1) ^ 2 * (GamBarF μ f / sF2 μ f) * nuR (ℓ ^ 2 / sF2 μ f)) + πg) +
        sF2 μ f * QB (ℓ ^ 2 / sF2 μ f) πg := by
  have hK0 : 0 ≤ K := (Ures_nonneg 0).trans (hK 0)
  have hPR : PRvecBound K := PRvec_of hK
  have hD2 := H.DF_sq_int
  refine ⟨hD2, ?_⟩
  rw [H.int_decomp (G := fun z => DF μ f z ^ 2) (H.meas_DF.pow_const 2) hD2]
  have hp := poly_gauss (cc0 (ℓ ^ 2 / sF2 μ f) πg) (cc1 (ℓ ^ 2 / sF2 μ f) πg)
    (cc2 (ℓ ^ 2 / sF2 μ f))
  -- the linear term as a function of `ζ`
  have hAm : Measurable (fun ζ : ℝ =>
      ∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ) := by
    have hF : Measurable (fun q : ℝ × Ω =>
        (PhiG (betaF μ f q.2 * (q.1 * √(GamBarF μ f)) / √(sig2F μ f q.2)) -
          PhiG (q.1 * √(GamBarF μ f) / sF μ f)) ^ 2) := by
      have hb : Measurable (fun q : ℝ × Ω => betaF μ f q.2) := H.meas_beta.comp measurable_snd
      have hs : Measurable (fun q : ℝ × Ω => √(sig2F μ f q.2)) :=
        (H.meas_sig.comp measurable_snd).sqrt
      have ha : Measurable (fun q : ℝ × Ω => q.1 * √(GamBarF μ f)) :=
        measurable_fst.mul_const _
      exact ((continuous_PhiG.measurable.comp ((hb.mul ha).div hs)).sub
        (continuous_PhiG.measurable.comp (ha.div_const _))).pow_const 2
    exact hF.stronglyMeasurable.integral_prod_right'.measurable
  have hAb : ∀ ζ : ℝ, ‖∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ‖ ≤ 1 := by
    intro ζ
    have := norm_integral_le_of_norm_le_const (μ := μ) (C := 1)
      (f := fun ω => (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact PhiG_diff_le_one _ _)
    simpa using this
  have hAi : Integrable (fun ζ : ℝ =>
      ∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono' hAm.aestronglyMeasurable (ae_of_all _ hAb)
  have r1 : Integrable (fun ζ : ℝ => ℓ ^ 2 *
      ∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ) (gaussianReal 0 1) := hAi.const_mul _
  have r2 : Integrable (fun _ : ℝ => K * (2 * hsF μ f / sF2 μ f + √2 * sF2 μ f * πg))
      (gaussianReal 0 1) := integrable_const _
  have r3 : Integrable (fun ζ : ℝ => sF2 μ f * (cc0 (ℓ ^ 2 / sF2 μ f) πg +
      cc1 (ℓ ^ 2 / sF2 μ f) πg * |ζ| + cc2 (ℓ ^ 2 / sF2 μ f) * ζ ^ 2) ^ 2) (gaussianReal 0 1) :=
    hp.1.const_mul _
  have r12 : Integrable (fun ζ : ℝ => ℓ ^ 2 *
      (∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ) +
      K * (2 * hsF μ f / sF2 μ f + √2 * sF2 μ f * πg)) (gaussianReal 0 1) := r1.add r2
  have r123 : Integrable (fun ζ : ℝ => ℓ ^ 2 *
      (∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ) +
      K * (2 * hsF μ f / sF2 μ f + √2 * sF2 μ f * πg) +
      sF2 μ f * (cc0 (ℓ ^ 2 / sF2 μ f) πg +
      cc1 (ℓ ^ 2 / sF2 μ f) πg * |ζ| + cc2 (ℓ ^ 2 / sF2 μ f) * ζ ^ 2) ^ 2) (gaussianReal 0 1) :=
    r12.add r3
  have hle := integral_mono_of_nonneg
    (f := fun ζ : ℝ => ∫ z', DF μ f (ζ • eF μ f + (projMat (eF μ f)).mulVec z') ^ 2
      ∂stdGauss (Fin m))
    (ae_of_all _ fun ζ => integral_nonneg fun _ => sq_nonneg _) r123
    (ae_of_all _ fun ζ => by
      have h := H.inner_sq_le hK0 hPR ζ
      rw [mul_pow, H.sF_sq] at h
      exact h)
  rw [integral_add r12 r3, integral_add r1 r2, integral_const_mul, integral_const_mul,
    integral_const_mul, hp.2, integral_const] at hle
  simp only [probReal_univ, one_smul] at hle
  have hlin := mul_le_mul_of_nonneg_left H.lin_term (sq_nonneg ℓ)
  have hKe : K * (2 * hsF μ f / sF2 μ f + √2 * sF2 μ f * πg) =
      2 * K * hsF μ f / sF2 μ f + K * √2 * sF2 μ f * πg := by ring
  rw [hKe] at hle
  unfold QB
  linarith

/-- **Lemma MF with `K₀ = (π − 2)/(4π)`.** -/
theorem MFHyp.lemmaMF (H : MFHyp μ f ℓ πg) :
    Integrable (fun z => DF μ f z ^ 2) (stdGauss (Fin m)) ∧
    ∫ z, DF μ f z ^ 2 ∂stdGauss (Fin m) ≤
      2 * K0 * hsF μ f / sF2 μ f + K0 * √2 * sF2 μ f * πg +
        ℓ ^ 2 * (1 / π * (2 * (ℓ ^ 2 / sF2 μ f) +
          4 * (√2 - 1) ^ 2 * (GamBarF μ f / sF2 μ f) * nuR (ℓ ^ 2 / sF2 μ f)) + πg) +
        sF2 μ f * QB (ℓ ^ 2 / sF2 μ f) πg :=
  H.lemmaMF_K Ures_le_K0

/-- **The cross term** (used in Lemma MP): for a measurable `h` with `E h(ā)² < ∞`:
`|E[𝖣·h(ā)]| ≤ s·√Q_B·(E h(ā)²)^{1/2}`. -/
theorem MFHyp.lemmaMF_cross (H : MFHyp μ f ℓ πg) {h : ℝ → ℝ} (hh : Measurable h)
    (hh2 : Integrable (fun z : Fin m → ℝ => h (z ⬝ᵥ fbar μ f) ^ 2) (stdGauss (Fin m))) :
    Integrable (fun z : Fin m → ℝ => DF μ f z * h (z ⬝ᵥ fbar μ f)) (stdGauss (Fin m)) ∧
    |∫ z, DF μ f z * h (z ⬝ᵥ fbar μ f) ∂stdGauss (Fin m)| ≤
      √(sF2 μ f * QB (ℓ ^ 2 / sF2 μ f) πg) *
        √(∫ z : Fin m → ℝ, h (z ⬝ᵥ fbar μ f) ^ 2 ∂stdGauss (Fin m)) := by
  have hD2 := H.DF_sq_int
  have hmh : Measurable (fun z : Fin m → ℝ => h (z ⬝ᵥ fbar μ f)) :=
    hh.comp (meas_dotT measurable_id measurable_const)
  have hmDh : Measurable (fun z : Fin m → ℝ => DF μ f z * h (z ⬝ᵥ fbar μ f)) :=
    H.meas_DF.mul hmh
  have hsum : Integrable (fun z : Fin m → ℝ => (DF μ f z ^ 2 + h (z ⬝ᵥ fbar μ f) ^ 2) / 2)
      (stdGauss (Fin m)) := (hD2.add hh2).div_const 2
  have hDh : Integrable (fun z : Fin m → ℝ => DF μ f z * h (z ⬝ᵥ fbar μ f)) (stdGauss (Fin m)) := by
    refine hsum.mono' hmDh.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;>
      nlinarith [sq_nonneg (DF μ f z - h (z ⬝ᵥ fbar μ f)),
        sq_nonneg (DF μ f z + h (z ⬝ᵥ fbar μ f))]
  refine ⟨hDh, ?_⟩
  -- the two functions of `ζ`
  have hU : Measurable (fun ζ : ℝ => ∫ z', DF μ f (ζ • eF μ f + (projMat (eF μ f)).mulVec z')
      ∂stdGauss (Fin m)) := meas_inner _ H.meas_DF
  have hV : Measurable (fun ζ : ℝ => h (ζ * nrm (fbar μ f))) :=
    hh.comp (measurable_id.mul_const _)
  have hU2 := H.bias_int
  have hVeq : ∀ ζ : ℝ, ∫ z' : Fin m → ℝ,
      h ((ζ • eF μ f + (projMat (eF μ f)).mulVec z') ⬝ᵥ fbar μ f) ^ 2 ∂stdGauss (Fin m) =
      h (ζ * nrm (fbar μ f)) ^ 2 := by
    intro ζ
    simp_rw [H.decomp_dot_fbar]
    simp
  have hV2 : Integrable (fun ζ : ℝ => h (ζ * nrm (fbar μ f)) ^ 2) (gaussianReal 0 1) := by
    have := (H.int_decomp_aux (G := fun z => h (z ⬝ᵥ fbar μ f) ^ 2) (hmh.pow_const 2)
      hh2).integral_prod_left
    refine this.congr (ae_of_all _ fun ζ => ?_)
    exact hVeq ζ
  have hVint : ∫ z : Fin m → ℝ, h (z ⬝ᵥ fbar μ f) ^ 2 ∂stdGauss (Fin m) =
      ∫ ζ, h (ζ * nrm (fbar μ f)) ^ 2 ∂gaussianReal 0 1 := by
    rw [H.int_decomp (G := fun z => h (z ⬝ᵥ fbar μ f) ^ 2) (hmh.pow_const 2) hh2]
    exact integral_congr_ae (ae_of_all _ hVeq)
  have hmain : ∫ z, DF μ f z * h (z ⬝ᵥ fbar μ f) ∂stdGauss (Fin m) =
      ∫ ζ, (∫ z', DF μ f (ζ • eF μ f + (projMat (eF μ f)).mulVec z') ∂stdGauss (Fin m)) *
        h (ζ * nrm (fbar μ f)) ∂gaussianReal 0 1 := by
    rw [H.int_decomp (G := fun z => DF μ f z * h (z ⬝ᵥ fbar μ f)) hmDh hDh]
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    beta_reduce
    simp_rw [H.decomp_dot_fbar]
    rw [integral_mul_const]
  have hCS := BstLean.Part132.integral_mul_le_sqrt hU hV hU2 hV2
  have h1 : |∫ ζ, (∫ z', DF μ f (ζ • eF μ f + (projMat (eF μ f)).mulVec z')
        ∂stdGauss (Fin m)) * h (ζ * nrm (fbar μ f)) ∂gaussianReal 0 1| ≤
      ∫ ζ, |∫ z', DF μ f (ζ • eF μ f + (projMat (eF μ f)).mulVec z') ∂stdGauss (Fin m)| *
        |h (ζ * nrm (fbar μ f))| ∂gaussianReal 0 1 := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    exact integral_congr_ae (ae_of_all _ fun ζ => abs_mul _ _)
  rw [hmain, hVint]
  refine h1.trans (hCS.2.trans ?_)
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt H.lemmaMF_bias) (Real.sqrt_nonneg _)


end BstLean.Part154
