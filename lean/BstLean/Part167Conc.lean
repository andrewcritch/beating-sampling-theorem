import BstLean.Part167Max

/-!
# Part 167 (file `Conc`): the transverse Gaussian integral (sub-lemma 6, first half)

No proof is left open; no `native_decide` or `axiom` is used.

Paper: proof of Lemma `t7:p07:LJ`, last paragraph: "Integrate `ζ` conditional on `(A₁, ξ)`. The
mean of `|M₀p + s_yM₀ζ|` is at most `√(|M₀p|² + s_y²‖M₀‖²_HS)`, and its Lipschitz constant is at
most `s_y‖M₀‖_op`."

For `γ` standard Gaussian in `ℝ^m`, `a ∈ ℝ^n`, a matrix `B` (`n × m`) with `|Bz| ≤ L|z|`:

* **`sec_mom`**: `E|a + Bγ|² = |a|² + ‖B‖²_F`.
* **`trans_mom`**: `E|a + Bγ|^{128} ≤ (√(|a|² + ‖B‖²_F) + (π/2)·(E|g|^{128})^{1/128}·L)^{128}`
  (Gaussian `L^p` Poincaré of Part 162 in place of the paper's concentration constant `k_ℓ`).
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part148 (EuLip)
open BstLean.Part153 (nrm nrm_nonneg)

variable {n m : ℕ}

lemma int_sq_shift (c v : ℝ) :
    Integrable (fun x : ℝ => (c + x) ^ 2) (gaussianReal 0 v.toNNReal) ∧
    ∫ x, (c + x) ^ 2 ∂gaussianReal 0 v.toNNReal = c ^ 2 + v.toNNReal := by
  have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v.toNNReal) :=
    (memLp_id_gaussianReal (μ := 0) (v := v.toNNReal) 2).integrable_sq
  have h1 : Integrable (fun x : ℝ => x) (gaussianReal 0 v.toNNReal) :=
    (memLp_id_gaussianReal (μ := 0) (v := v.toNNReal) 1).integrable le_rfl
  have e : (fun x : ℝ => (c + x) ^ 2) = fun x => c ^ 2 + (2 * c * x + x ^ 2) := by
    funext x; ring
  rw [e]
  refine ⟨(integrable_const _).add ((h1.const_mul _).add h2), ?_⟩
  have h12 : Integrable (fun x : ℝ => 2 * c * x + x ^ 2) (gaussianReal 0 v.toNNReal) :=
    (h1.const_mul (2 * c)).add h2
  have h1' : Integrable (fun x : ℝ => 2 * c * x) (gaussianReal 0 v.toNNReal) := h1.const_mul _
  rw [integral_add (integrable_const _) h12, integral_add h1' h2, integral_const_mul,
    integral_id_gaussianReal]
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := v.toNNReal)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hv
  simp only [integral_id_gaussianReal, sub_zero] at hv
  simp [hv]

/-- **`E|a + Bγ|² = |a|² + ‖B‖²_F`.** -/
theorem sec_mom (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    Integrable (fun γ : Fin m → ℝ => normSq (a + B *ᵥ γ)) (stdGauss (Fin m)) ∧
    ∫ γ, normSq (a + B *ᵥ γ) ∂stdGauss (Fin m) = normSq a + ∑ i, ∑ j, B i j ^ 2 := by
  have hrow : ∀ i : Fin n, Integrable (fun γ : Fin m → ℝ => (a i + γ ⬝ᵥ B i) ^ 2)
      (stdGauss (Fin m)) ∧
      ∫ γ, (a i + γ ⬝ᵥ B i) ^ 2 ∂stdGauss (Fin m) = a i ^ 2 + ∑ j, B i j ^ 2 := by
    intro i
    have hmap := BstLean.Part131.stdGauss_dot (ι := Fin m) (B i)
    have hm : Measurable (fun γ : Fin m → ℝ => γ ⬝ᵥ B i) :=
      (continuous_id.dotProduct continuous_const).measurable
    obtain ⟨hI, hE⟩ := int_sq_shift (a i) (B i ⬝ᵥ B i)
    have hD : 0 ≤ B i ⬝ᵥ B i := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    constructor
    · rw [← hmap] at hI
      exact (integrable_map_measure (by fun_prop) hm.aemeasurable).mp hI
    · have hmi := integral_map (μ := stdGauss (Fin m)) hm.aemeasurable
        (f := fun x : ℝ => (a i + x) ^ 2) (Continuous.aestronglyMeasurable (by fun_prop))
      rw [hmap] at hmi
      rw [← hmi, hE, Real.coe_toNNReal _ hD]
      simp only [dotProduct, sq]
  have e : ∀ γ : Fin m → ℝ, normSq (a + B *ᵥ γ) = ∑ i, (a i + γ ⬝ᵥ B i) ^ 2 := by
    intro γ; unfold normSq
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, mulVec, dotProduct_comm]
  simp_rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => (hrow i).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => (hrow i).1]
  simp_rw [fun i => (hrow i).2]
  rw [Finset.sum_add_distrib]; rfl

/-- **The transverse Gaussian moment**: `E|a + Bγ|^{128} ≤ (√(|a|² + ‖B‖²_F) + C L)^{128}`,
`C = (π/2)(E|g|^{128})^{1/128}`. -/
theorem trans_mom (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z, nrm (B *ᵥ z) ≤ L * nrm z) :
    ∫⁻ γ, ENNReal.ofReal (nrm (a + B *ᵥ γ) ^ 128) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((√(normSq a + ∑ i, ∑ j, B i j ^ 2) +
        π / 2 * BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) * L) ^ 128) := by
  set f : (Fin m → ℝ) → ℝ := fun γ => nrm (a + B *ᵥ γ) with hf
  have hlip : EuLip f L := by
    intro x y
    have h1 : |f x - f y| ≤ nrm ((a + B *ᵥ x) - (a + B *ᵥ y)) := by
      have := BstLean.Part153.nrm_tri3 (a + B *ᵥ x) (a + B *ᵥ y)
      have := BstLean.Part153.nrm_tri3 (a + B *ᵥ y) (a + B *ᵥ x)
      have e : nrm ((a + B *ᵥ y) - (a + B *ᵥ x)) = nrm ((a + B *ᵥ x) - (a + B *ᵥ y)) := by
        unfold nrm normSq; congr 1; exact Finset.sum_congr rfl fun i _ => by
          simp only [Pi.sub_apply]; ring
      rw [abs_le]; constructor <;> linarith
    have e2 : (a + B *ᵥ x) - (a + B *ᵥ y) = B *ᵥ (x - y) := by
      rw [Matrix.mulVec_sub]; abel
    rw [e2] at h1
    refine h1.trans ((hL _).trans (le_of_eq ?_))
    rfl
  obtain ⟨hI2, hE2⟩ := sec_mom a B
  set V := normSq a + ∑ i, ∑ j, B i j ^ 2 with hV
  have hV0 : 0 ≤ V := add_nonneg (normSq_nonneg a)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hfi : Integrable f (stdGauss (Fin m)) :=
    (BstLean.Part151.lip_memLp hL0 hlip).integrable one_le_two
  set E := ∫ γ, f γ ∂stdGauss (Fin m) with hEdef
  -- `E f ≤ √V` (Jensen)
  have hEle : E ≤ √V := by
    have hE0 : 0 ≤ E := integral_nonneg fun γ => nrm_nonneg _
    have hsq : E ^ 2 ≤ V := by
      have hJ := (convexOn_pow 2).map_integral_le (μ := stdGauss (Fin m)) (f := f)
        (continuous_pow 2).continuousOn isClosed_Ici
        (Filter.Eventually.of_forall fun γ => Set.mem_Ici.mpr (nrm_nonneg _)) hfi
        (by
          have : (fun γ => f γ ^ 2) = fun γ => normSq (a + B *ᵥ γ) := by
            funext γ; simp only [hf, nrm]; rw [Real.sq_sqrt (normSq_nonneg _)]
          simp only [Function.comp_def]; rw [this]; exact hI2)
      try simp only [Function.comp_def] at hJ
      have : (fun γ => f γ ^ 2) = fun γ => normSq (a + B *ᵥ γ) := by
        funext γ; simp only [hf, nrm]; rw [Real.sq_sqrt (normSq_nonneg _)]
      rw [this, hE2] at hJ
      exact hJ
    exact Real.le_sqrt_of_sq_le hsq
  -- Poincaré for the deviation
  have hP := BstLean.Part162.poincare_p_lint hL0 hlip (p := 128) (by norm_num)
  have hgrad : ∫ x, √(BstLean.Part151.gradSq f x) ^ 128 ∂stdGauss (Fin m) ≤ L ^ 128 := by
    have hb : ∀ x, √(BstLean.Part151.gradSq f x) ^ 128 ≤ L ^ 128 := fun x =>
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (by
        rw [Real.sqrt_le_left hL0]; exact BstLean.Part151.gradSq_le hL0 hlip x) 128
    calc ∫ x, √(BstLean.Part151.gradSq f x) ^ 128 ∂stdGauss (Fin m)
        ≤ ∫ _x, L ^ 128 ∂stdGauss (Fin m) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
            (integrable_const _) (Filter.Eventually.of_forall hb)
      _ = L ^ 128 := by simp
  set C := π / 2 * BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) with hC
  have hg0 := BstLean.Part162.gmom_nonneg 128
  have hC0 : 0 ≤ C := by positivity
  have hgg : (BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128)) ^ (128 : ℕ) =
      BstLean.Part162.gmom 128 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hg0]; norm_num
  have hCL : (π / 2) ^ 128 * (BstLean.Part162.gmom 128 * L ^ 128) = (C * L) ^ 128 := by
    rw [hC, mul_pow, mul_pow, hgg]; ring
  have hdev : ∫⁻ γ, ENNReal.ofReal (|f γ - E| ^ 128) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((C * L) ^ 128) := by
    refine hP.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hCL]
    gcongr
  -- Minkowski with the constant `E`
  by_cases hCL0 : C * L = 0
  · -- `f` is a.e. constant
    rw [hCL0] at hdev
    rw [zero_pow (by norm_num), ENNReal.ofReal_zero, nonpos_iff_eq_zero] at hdev
    have hae : ∀ᵐ γ ∂stdGauss (Fin m), ENNReal.ofReal (|f γ - E| ^ 128) = 0 := by
      have hmeas : Measurable (fun γ => ENNReal.ofReal (|f γ - E| ^ 128)) :=
        ENNReal.measurable_ofReal.comp (((hlip.continuous hL0).measurable.sub_const _).abs.pow_const _)
      exact (lintegral_eq_zero_iff hmeas).mp hdev
    have hpt : ∀ᵐ γ ∂stdGauss (Fin m), ENNReal.ofReal (f γ ^ 128) ≤
        ENNReal.ofReal ((√V + C * L) ^ 128) := by
      filter_upwards [hae] with γ hγ
      apply ENNReal.ofReal_le_ofReal
      have h0 : |f γ - E| ^ 128 ≤ 0 := ENNReal.ofReal_eq_zero.mp hγ
      have h1 : f γ - E = 0 := by
        have := pow_eq_zero_iff (n := 128) (by norm_num) |>.mp
          (le_antisymm h0 (pow_nonneg (abs_nonneg _) _))
        exact abs_eq_zero.mp this
      have hfE : f γ = E := by linarith
      rw [hfE, hCL0, add_zero]
      exact pow_le_pow_left₀ (integral_nonneg fun γ => nrm_nonneg _) hEle 128
    refine (lintegral_mono_ae hpt).trans ?_
    rw [lintegral_const, measure_univ, mul_one, hCL0, add_zero]
  · have hCLp : 0 < C * L := lt_of_le_of_ne (mul_nonneg hC0 hL0) (Ne.symm hCL0)
    by_cases hE0 : E = 0
    · -- `f = |f − 0|`
      have hpt : ∀ γ, ENNReal.ofReal (f γ ^ 128) = ENNReal.ofReal (|f γ - E| ^ 128) := by
        intro γ; rw [hE0, sub_zero, abs_of_nonneg (nrm_nonneg _)]
      refine (le_of_eq (lintegral_congr hpt)).trans (hdev.trans ?_)
      refine (ENNReal.ofReal_le_ofReal ?_)
      exact pow_le_pow_left₀ hCLp.le (by have := Real.sqrt_nonneg V; linarith) 128
    · have hEp : 0 < E := lt_of_le_of_ne (integral_nonneg fun γ => nrm_nonneg _) (Ne.symm hE0)
      have hpt : ∀ γ, ENNReal.ofReal (f γ ^ 128) ≤
          ENNReal.ofReal ((E + C * L) ^ 127 * (E ^ 128 / E ^ 127)) +
            ENNReal.ofReal ((E + C * L) ^ 127 / (C * L) ^ 127) *
              ENNReal.ofReal (|f γ - E| ^ 128) := by
        intro γ
        have q1 : 0 ≤ (E + C * L) ^ 127 * (E ^ 128 / E ^ 127) :=
          mul_nonneg (pow_nonneg (by linarith) _) (div_nonneg (pow_nonneg hEp.le _)
            (pow_nonneg hEp.le _))
        have q2 : 0 ≤ (E + C * L) ^ 127 / (C * L) ^ 127 :=
          div_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hCLp.le _)
        rw [← ENNReal.ofReal_mul q2, ← ENNReal.ofReal_add q1
          (mul_nonneg q2 (pow_nonneg (abs_nonneg _) _))]
        apply ENNReal.ofReal_le_ofReal
        have h1 : f γ ≤ E + |f γ - E| := by
          have := le_abs_self (f γ - E); linarith
        have h2 := pow_add_split hEp.le (abs_nonneg (f γ - E)) hEp hCLp 127
        calc f γ ^ 128 ≤ (E + |f γ - E|) ^ 128 :=
              pow_le_pow_left₀ (nrm_nonneg _) h1 128
          _ ≤ _ := h2
          _ = _ := by ring
      refine (lintegral_mono hpt).trans ?_
      have hmeas : Measurable (fun γ => ENNReal.ofReal (|f γ - E| ^ 128)) :=
        ENNReal.measurable_ofReal.comp
          (((hlip.continuous hL0).measurable.sub_const _).abs.pow_const _)
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_const_mul _ hmeas]
      calc ENNReal.ofReal ((E + C * L) ^ 127 * (E ^ 128 / E ^ 127)) +
            ENNReal.ofReal ((E + C * L) ^ 127 / (C * L) ^ 127) *
              ∫⁻ γ, ENNReal.ofReal (|f γ - E| ^ 128) ∂stdGauss (Fin m)
          ≤ ENNReal.ofReal ((E + C * L) ^ 127 * (E ^ 128 / E ^ 127)) +
            ENNReal.ofReal ((E + C * L) ^ 127 / (C * L) ^ 127) *
              ENNReal.ofReal ((C * L) ^ 128) := by gcongr
        _ = ENNReal.ofReal ((E + C * L) ^ 128) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
            congr 1
            obtain ⟨T, hT⟩ : ∃ T, T = E + C * L := ⟨_, rfl⟩
            have k1 : E ^ 128 / E ^ 127 = E := by
              rw [pow_succ E 127]; field_simp
            have k2 : (E + C * L) ^ 127 / (C * L) ^ 127 * (C * L) ^ 128 =
                (E + C * L) ^ 127 * (C * L) := by
              rw [pow_succ (C * L) 127]; field_simp
            rw [k1, k2, ← mul_add, ← pow_succ]
        _ ≤ ENNReal.ofReal ((√V + C * L) ^ 128) := by
            apply ENNReal.ofReal_le_ofReal
            exact pow_le_pow_left₀ (by positivity) (by linarith) 128

end BstLean.Part167
