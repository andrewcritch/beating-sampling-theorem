import BstLean.Part151TR
import BstLean.Part151FStage
import BstLean.Part148GC

/-!
# Part 151, item 4 (b): Lemma SA (the sampling term)

Role: `delegations/statements/p151-spec.md`, item 4 (b). Paper source:
`proofs/option-n/theorem5-09-fluctuation.tex`, Lemma SA.

`θ = (F₁, F₂)` are the hidden matrices of `F`, `z_F(y) = hid2 F₁ F₂ y`, `t_F = 2/m`. For a centre
`c` and a scale `σ`: `zS θ c σ γ = z_F(c + σγ)`; `dSamp θ c σ k η = Δ_s` (the mean of `k`
copies minus the Gaussian mean); `Ts θ c σ k η = T_s = √(t_F)·|Δ_s|`.

* `mean_sq_pi`: the second moment of the centred mean of `k` independent copies is at most
  `E f²/k`.
* **`lemmaSA_fixed`**: `E_η |Δ_s|² ≤ E_γ|z_F(c + σγ)|²/k`, for fixed `θ`, `c`, `σ`.
* **`lemmaSA_mean`**: `E_{F₁,F₂} E_η t_F|Δ_s|² ≤ (2/n)(|c|² + nσ²)/k`.
* `gamK_eq_gaussMat`: `k` standard Gaussian vectors of `ℝⁿ` are a `k × n` Gaussian matrix.
* **`lemmaSA_lip`**: if `z_F` is `L`-Lipschitz, `η ↦ T_s` is Lipschitz with constant
  `√(t_F)·L·|σ|/√k`.
* **`lemmaSA_conc`**, `lemmaSA_conc'`: the upper tail of `T_s` (with the constant `π²/4` of
  Part 148 in the place of the constant `1` of the fact (G1) of the document).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part130 BstLean.Part131
open BstLean.Part132 (nrm nrm_sq nrm_nonneg hid2_sq)
open BstLean.Part136 (HidParam hidGauss continuous_hid2_joint)
open BstLean.Part139 (gamK)
open BstLean.Part149 (stdGauss_normSq)

/-! ## The mean of independent copies -/

section pi

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The second moment of the centred mean of `k` independent copies**:
`E((1/k)Σ_j f(ω_j) − E f)² = Var f/k ≤ E f²/k`. -/
theorem mean_sq_pi (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ)
    {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun us : Fin k → Ω => ((k : ℝ)⁻¹ * ∑ j, f (us j) - ∫ ω, f ω ∂μ) ^ 2)
        (Measure.pi fun _ : Fin k => μ) ∧
      ∫ us, ((k : ℝ)⁻¹ * ∑ j, f (us j) - ∫ ω, f ω ∂μ) ^ 2 ∂(Measure.pi fun _ : Fin k => μ) ≤
        (∫ ω, f ω ^ 2 ∂μ) / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set π := Measure.pi fun _ : Fin k => μ with hπ
  set S : (Fin k → Ω) → ℝ := ∑ j : Fin k, fun us => f (us j) with hS
  have hSapp : ∀ us, S us = ∑ j, f (us j) := fun us => by simp [hS, Finset.sum_apply]
  have hj : ∀ j : Fin k, MemLp (fun us : Fin k → Ω => f (us j)) 2 π := fun j =>
    hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin k => μ) j)
  have hSm : MemLp S 2 π := memLp_finsetSum' _ fun j _ => hj j
  have hvar : Var[S; π] = k * Var[f; μ] := by
    have h := variance_sum_pi (μ := fun _ : Fin k => μ) (X := fun _ : Fin k => f) fun _ => hf
    rw [hS, hπ, h]
    simp
  have hmean : ∫ us, S us ∂π = k * ∫ ω, f ω ∂μ := by
    simp_rw [hSapp]
    rw [integral_finsetSum _ fun j _ => (hj j).integrable (by norm_num)]
    have e : ∀ j : Fin k, ∫ us : Fin k → Ω, f (us j) ∂π = ∫ ω, f ω ∂μ := fun j => by
      have h := (measurePreserving_eval (fun _ : Fin k => μ) j).map_eq
      rw [hπ]
      conv_rhs => rw [← h]
      rw [integral_map (measurable_pi_apply j).aemeasurable]
      rw [h]; exact hf.aestronglyMeasurable
    simp_rw [e]
    simp
  have hveq : Var[S; π] = ∫ us, (S us - ∫ us, S us ∂π) ^ 2 ∂π :=
    variance_eq_integral hSm.aestronglyMeasurable.aemeasurable
  have hpt : ∀ us : Fin k → Ω, ((k : ℝ)⁻¹ * ∑ j, f (us j) - ∫ ω, f ω ∂μ) ^ 2 =
      ((k : ℝ)⁻¹) ^ 2 * (S us - ∫ us, S us ∂π) ^ 2 := by
    intro us
    rw [hmean, hSapp]
    field_simp
  have hint : Integrable (fun us => (S us - ∫ us, S us ∂π) ^ 2) π :=
    (hSm.sub (memLp_const _)).integrable_sq
  refine ⟨?_, ?_⟩
  · simp_rw [hpt]
    exact hint.const_mul _
  · simp_rw [hpt]
    rw [integral_const_mul, ← hveq, hvar]
    have h1 : Var[f; μ] ≤ ∫ ω, f ω ^ 2 ∂μ := by
      have h := variance_le_expectation_sq (μ := μ) hf.aestronglyMeasurable
      simpa using h
    have h0 : 0 ≤ Var[f; μ] := variance_nonneg _ _
    rw [show ((k : ℝ)⁻¹) ^ 2 * (k * Var[f; μ]) = Var[f; μ] / k by field_simp]
    exact div_le_div_of_nonneg_right h1 hk0.le

end pi

/-! ## The sampling term -/

variable {n m : ℕ}

/-- `z_F(c + σγ)`. -/
noncomputable def zS (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) (γ : Fin n → ℝ) : Fin m → ℝ :=
  hid2 θ.1 θ.2 (c + σ • γ)

/-- `Δ_s`: the mean of `z_F(c + σ·η_j)` over the `k` Gaussian vectors, minus its Gaussian mean. -/
noncomputable def dSamp (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) (k : ℕ)
    (η : Fin k → Fin n → ℝ) : Fin m → ℝ :=
  fun i => (k : ℝ)⁻¹ * ∑ j, zS θ c σ (η j) i - ∫ γ, zS θ c σ γ i ∂stdGauss (Fin n)

/-- `T_s = √(t_F)·|Δ_s|`, `t_F = 2/m`. -/
noncomputable def Ts (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) (k : ℕ)
    (η : Fin k → Fin n → ℝ) : ℝ :=
  √(2 / (m : ℝ) * normSq (dSamp θ c σ k η))

lemma continuous_zS (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) : Continuous (zS θ c σ) := by
  unfold zS
  exact continuous_hid2_joint.comp (continuous_const.prodMk (by fun_prop))

lemma normSq_add_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    normSq (a + b) ≤ 2 * normSq a + 2 * normSq b := by
  unfold normSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (a i - b i)]

lemma shift_integrable (c : Fin n → ℝ) (σ : ℝ) :
    Integrable (fun γ : Fin n → ℝ => normSq (c + σ • γ)) (stdGauss (Fin n)) := by
  have hdom : Integrable (fun γ : Fin n → ℝ => 2 * normSq c + 2 * (σ ^ 2 * normSq γ))
      (stdGauss (Fin n)) :=
    (integrable_const _).add (((stdGauss_normSq n).1.const_mul _).const_mul _)
  have hc : Continuous (fun γ : Fin n → ℝ => normSq (c + σ • γ)) := by
    unfold normSq; fun_prop
  refine hdom.mono' hc.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun γ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (normSq_nonneg _)]
  have h := normSq_add_le c (σ • γ)
  rwa [normSq_smul] at h

lemma zS_normSq_integrable (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) :
    Integrable (fun γ : Fin n → ℝ => normSq (zS θ c σ γ)) (stdGauss (Fin n)) := by
  have hdom := ((shift_integrable c σ).const_mul (frob θ.1)).const_mul (frob θ.2)
  have hc : Continuous (fun γ : Fin n → ℝ => normSq (zS θ c σ γ)) := by
    have h := continuous_zS θ c σ
    unfold normSq; fun_prop
  refine hdom.mono' hc.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun γ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (normSq_nonneg _)]
  exact normSq_hid2_le θ.1 θ.2 _

lemma zS_coord_memLp (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) (i : Fin m) :
    MemLp (fun γ : Fin n → ℝ => zS θ c σ γ i) 2 (stdGauss (Fin n)) := by
  have hc : Continuous (fun γ : Fin n → ℝ => zS θ c σ γ i) :=
    (continuous_apply i).comp (continuous_zS θ c σ)
  rw [memLp_two_iff_integrable_sq hc.measurable.aestronglyMeasurable]
  refine (zS_normSq_integrable θ c σ).mono' (hc.measurable.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun γ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold normSq
  exact Finset.single_le_sum (f := fun j => zS θ c σ γ j ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

/-- The squared length of `Δ_s` is integrable, and its mean is at most `E|z_F(c + σγ)|²/k`. -/
theorem lemmaSA_fixed_int (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun η : Fin k → Fin n → ℝ => normSq (dSamp θ c σ k η)) (gamK k n) ∧
      ∫ η, normSq (dSamp θ c σ k η) ∂gamK k n ≤
        (∫ γ, normSq (zS θ c σ γ) ∂stdGauss (Fin n)) / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hi := fun i : Fin m => mean_sq_pi (stdGauss (Fin n)) (zS_coord_memLp θ c σ i) hk
  have hI : Integrable (fun η : Fin k → Fin n → ℝ => normSq (dSamp θ c σ k η)) (gamK k n) := by
    unfold normSq dSamp
    exact integrable_finsetSum _ fun i _ => (hi i).1
  refine ⟨hI, ?_⟩
  have e1 : ∫ η, normSq (dSamp θ c σ k η) ∂gamK k n =
      ∑ i, ∫ η : Fin k → Fin n → ℝ, dSamp θ c σ k η i ^ 2 ∂gamK k n := by
    unfold normSq
    exact integral_finsetSum _ fun i _ => (hi i).1
  have e2 : ∫ γ, normSq (zS θ c σ γ) ∂stdGauss (Fin n) =
      ∑ i, ∫ γ : Fin n → ℝ, zS θ c σ γ i ^ 2 ∂stdGauss (Fin n) := by
    unfold normSq
    exact integral_finsetSum _ fun i _ => (zS_coord_memLp θ c σ i).integrable_sq
  rw [e1, e2, Finset.sum_div]
  exact Finset.sum_le_sum fun i _ => (hi i).2

/-- **Lemma SA, second-moment form, fixed `F`**: `E_η|Δ_s|² ≤ E_γ|z_F(c + σγ)|²/k`. -/
theorem lemmaSA_fixed (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ η, ENNReal.ofReal (normSq (dSamp θ c σ k η)) ∂gamK k n ≤
      ENNReal.ofReal ((∫ γ, normSq (zS θ c σ γ) ∂stdGauss (Fin n)) / k) := by
  obtain ⟨hI, hle⟩ := lemmaSA_fixed_int θ c σ hk
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun η => normSq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hle

/-- `E|c + σγ|² = |c|² + nσ²`. -/
lemma shift_second (c : Fin n → ℝ) (σ : ℝ) :
    ∫ γ, normSq (c + σ • γ) ∂stdGauss (Fin n) = normSq c + n * σ ^ 2 := by
  have h1 : ∫ x : ℝ, x ∂gaussianReal 0 1 = 0 := integral_id_gaussianReal
  have h2 : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    rw [gaussMom_eq]; norm_num [gaussMom]
  have i1 : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
    simpa using integrable_pow_gauss 1
  have i2 := integrable_pow_gauss 2
  have hcoord : ∀ i : Fin n, Integrable (fun x : ℝ => (c i + σ * x) ^ 2) (gaussianReal 0 1) ∧
      ∫ x : ℝ, (c i + σ * x) ^ 2 ∂gaussianReal 0 1 = c i ^ 2 + σ ^ 2 := by
    intro i
    have e : (fun x : ℝ => (c i + σ * x) ^ 2) =
        fun x => c i ^ 2 + (2 * c i * σ) * x + σ ^ 2 * x ^ 2 := by funext x; ring
    have ia : Integrable (fun x : ℝ => c i ^ 2 + (2 * c i * σ) * x) (gaussianReal 0 1) :=
      (integrable_const _).add (i1.const_mul _)
    rw [e]
    refine ⟨ia.add (i2.const_mul _), ?_⟩
    rw [integral_add ia (i2.const_mul _), integral_add (integrable_const _) (i1.const_mul _),
      integral_const_mul, integral_const_mul, h1, h2]
    simp
  unfold stdGauss normSq
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_finsetSum _ fun i _ =>
    integrable_comp_eval (μ := fun _ : Fin n => gaussianReal 0 1) (i := i) (hcoord i).1]
  have e : ∀ i : Fin n, ∫ γ : Fin n → ℝ, (c i + σ * γ i) ^ 2
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = c i ^ 2 + σ ^ 2 := fun i => by
    rw [integral_comp_eval (μ := fun _ : Fin n => gaussianReal 0 1) (i := i)
      (f := fun x : ℝ => (c i + σ * x) ^ 2) (hcoord i).1.aestronglyMeasurable]
    exact (hcoord i).2
  simp_rw [e]
  rw [Finset.sum_add_distrib]
  simp

/-- **Lemma SA, mean form**: `E_{F₁,F₂} E_η t_F·|Δ_s|² ≤ (2/n)·(|c|² + nσ²)/k`, `t_F = 2/m`.
(With `|c|² + nσ² ≈ 2` this is `S/k`, `S = 4/n`.) -/
theorem lemmaSA_mean (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ θ, ∫⁻ η, ENNReal.ofReal (2 / (m : ℝ) * normSq (dSamp θ c σ k η)) ∂gamK k n
        ∂hidGauss n m ≤
      ENNReal.ofReal (2 / (n : ℝ) * (normSq c + n * σ ^ 2) / k) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hA0 : (0 : ℝ) ≤ 2 / (m : ℝ) / k := by positivity
  -- fixed `θ`
  have h1 : ∀ θ : HidParam n m,
      ∫⁻ η, ENNReal.ofReal (2 / (m : ℝ) * normSq (dSamp θ c σ k η)) ∂gamK k n ≤
        ENNReal.ofReal (2 / (m : ℝ) / k) *
          ∫⁻ γ, ENNReal.ofReal (normSq (zS θ c σ γ)) ∂stdGauss (Fin n) := by
    intro θ
    have h := lemmaSA_fixed θ c σ hk
    have e : ∀ η : Fin k → Fin n → ℝ,
        ENNReal.ofReal (2 / (m : ℝ) * normSq (dSamp θ c σ k η)) =
          ENNReal.ofReal (2 / (m : ℝ)) * ENNReal.ofReal (normSq (dSamp θ c σ k η)) := fun η =>
      ENNReal.ofReal_mul (by positivity)
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal (zS_normSq_integrable θ c σ)
        (Filter.Eventually.of_forall fun γ => normSq_nonneg _),
      ← ENNReal.ofReal_mul hA0]
    refine (mul_le_mul' le_rfl h).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    ring
  refine (lintegral_mono h1).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- exchange the integrals
  have hjm : Measurable (fun q : HidParam n m × (Fin n → ℝ) =>
      ENNReal.ofReal (normSq (zS q.1 c σ q.2))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have hc : Continuous (fun q : HidParam n m × (Fin n → ℝ) => hid2 q.1.1 q.1.2 (c + σ • q.2)) :=
      continuous_hid2_joint.comp
        (continuous_fst.prodMk (continuous_const.add (continuous_snd.const_smul σ)))
    unfold zS normSq
    exact (continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hc).pow 2).measurable
  rw [lintegral_lintegral_swap hjm.aemeasurable]
  have h2 : ∀ γ : Fin n → ℝ, ∫⁻ θ : HidParam n m, ENNReal.ofReal (normSq (zS θ c σ γ))
      ∂hidGauss n m = ENNReal.ofReal ((m : ℝ) / n * normSq (c + σ • γ)) := by
    intro γ
    obtain ⟨hi, he⟩ := hid2_sq (m₁ := m) (m₂ := m) (k := n) (v₁ := 2 / (n : ℝ))
      (v₂ := 2 / (m : ℝ)) (by positivity) (by positivity) (c + σ • γ)
    unfold hidGauss zS
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun θ => normSq_nonneg _), he]
    congr 1
    field_simp
  simp_rw [h2]
  have e3 : ∀ γ : Fin n → ℝ, ENNReal.ofReal ((m : ℝ) / n * normSq (c + σ • γ)) =
      ENNReal.ofReal ((m : ℝ) / n) * ENNReal.ofReal (normSq (c + σ • γ)) := fun γ =>
    ENNReal.ofReal_mul (by positivity)
  simp_rw [e3]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal (shift_integrable c σ)
      (Filter.Eventually.of_forall fun γ => normSq_nonneg _), shift_second,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hA0]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  field_simp

/-! ## `k` Gaussian vectors are a Gaussian matrix -/

/-- **`k` independent standard Gaussian vectors of `ℝⁿ` are the rows of a `k × n` matrix with
independent standard Gaussian entries.** -/
theorem gamK_eq_gaussMat (k n : ℕ) : gamK k n = gaussMat k n 1 := by
  have e1 : rowDist n 1 = stdGauss (Fin n) := by
    unfold rowDist
    have : (fun ξ : Fin n → ℝ => √(1 : ℝ) • ξ) = id := by
      funext ξ; simp
    rw [this, Measure.map_id]
  have h := gaussMat_rows k n 1
  rw [e1] at h
  rw [h]
  exact (Measure.map_id (μ := gamK k n)).symm

/-! ## The Lipschitz property and the concentration -/

lemma Ts_eq (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) (k : ℕ) (η : Fin k → Fin n → ℝ) :
    Ts θ c σ k η = √(2 / (m : ℝ)) * nrm (dSamp θ c σ k η) := by
  unfold Ts nrm
  exact Real.sqrt_mul (by positivity) _

lemma nrm_sub_abs {ι : Type*} [Fintype ι] (a b : ι → ℝ) : |nrm a - nrm b| ≤ nrm (a - b) := by
  have h1 := BstLean.Part140.nrm_add_le' b (a - b)
  have h2 := BstLean.Part140.nrm_add_le' a (b - a)
  have e1 : b + (a - b) = a := by abel
  have e2 : a + (b - a) = b := by abel
  have e3 : nrm (b - a) = nrm (a - b) := by
    unfold nrm normSq
    congr 1
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  rw [e1] at h1
  rw [e2, e3] at h2
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- **Lemma SA, the Lipschitz property.** If `z_F` is `L`-Lipschitz for the Euclidean norms, then
`η ↦ T_s` is Lipschitz with constant `ℓ_s = √(t_F)·L·|σ|/√k` for the Euclidean norm of
`(η_1, …, η_k)`. -/
theorem lemmaSA_lip (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) {L : ℝ}
    (hL0 : 0 ≤ L)
    (hL : ∀ y y', normSq (hid2 θ.1 θ.2 y - hid2 θ.1 θ.2 y') ≤ L ^ 2 * normSq (y - y'))
    (η η' : Fin k → Fin n → ℝ) :
    |Ts θ c σ k η - Ts θ c σ k η'| ≤
      √(2 / (m : ℝ)) * L * |σ| / √(k : ℝ) * √(∑ j, ∑ i, (η j i - η' j i) ^ 2) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set Sq : ℝ := ∑ j, ∑ i, (η j i - η' j i) ^ 2 with hSq
  have hSq0 : 0 ≤ Sq := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  -- the squared distance of the two feature errors
  have hd : normSq (dSamp θ c σ k η - dSamp θ c σ k η') ≤ L ^ 2 * σ ^ 2 / k * Sq := by
    have hcoord : ∀ i : Fin m, (dSamp θ c σ k η - dSamp θ c σ k η') i ^ 2 ≤
        (k : ℝ)⁻¹ * ∑ j, (zS θ c σ (η j) i - zS θ c σ (η' j) i) ^ 2 := by
      intro i
      have e : (dSamp θ c σ k η - dSamp θ c σ k η') i =
          (k : ℝ)⁻¹ * ∑ j, (zS θ c σ (η j) i - zS θ c σ (η' j) i) := by
        simp only [Pi.sub_apply, dSamp, Finset.sum_sub_distrib]
        ring
      rw [e, mul_pow]
      have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k)))
        (f := fun j => zS θ c σ (η j) i - zS θ c σ (η' j) i)
      rw [Finset.card_univ, Fintype.card_fin] at h
      have hk2 : (0 : ℝ) ≤ ((k : ℝ)⁻¹) ^ 2 := by positivity
      calc ((k : ℝ)⁻¹) ^ 2 * (∑ j, (zS θ c σ (η j) i - zS θ c σ (η' j) i)) ^ 2
          ≤ ((k : ℝ)⁻¹) ^ 2 * (k * ∑ j, (zS θ c σ (η j) i - zS θ c σ (η' j) i) ^ 2) :=
            mul_le_mul_of_nonneg_left h hk2
        _ = _ := by field_simp
    have hrow : ∀ j : Fin k, normSq (zS θ c σ (η j) - zS θ c σ (η' j)) ≤
        L ^ 2 * (σ ^ 2 * ∑ i, (η j i - η' j i) ^ 2) := by
      intro j
      have h := hL (c + σ • η j) (c + σ • η' j)
      have e : c + σ • η j - (c + σ • η' j) = σ • (η j - η' j) := by
        rw [smul_sub]; abel
      rw [e, normSq_smul] at h
      exact h
    calc normSq (dSamp θ c σ k η - dSamp θ c σ k η')
        ≤ ∑ i : Fin m, (k : ℝ)⁻¹ * ∑ j, (zS θ c σ (η j) i - zS θ c σ (η' j) i) ^ 2 :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = (k : ℝ)⁻¹ * ∑ j, normSq (zS θ c σ (η j) - zS θ c σ (η' j)) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          rfl
      _ ≤ (k : ℝ)⁻¹ * ∑ j, L ^ 2 * (σ ^ 2 * ∑ i, (η j i - η' j i) ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hrow j) (by positivity)
      _ = L ^ 2 * σ ^ 2 / k * Sq := by
          rw [hSq, ← Finset.mul_sum, ← Finset.mul_sum]
          field_simp
  have hn2 : nrm (dSamp θ c σ k η - dSamp θ c σ k η') ≤ L * |σ| / √(k : ℝ) * √Sq := by
    unfold nrm
    refine (Real.sqrt_le_sqrt hd).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_div (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_sq hL0, Real.sqrt_sq_eq_abs]
  rw [Ts_eq, Ts_eq, ← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc √(2 / (m : ℝ)) * |nrm (dSamp θ c σ k η) - nrm (dSamp θ c σ k η')|
      ≤ √(2 / (m : ℝ)) * (L * |σ| / √(k : ℝ) * √Sq) :=
        mul_le_mul_of_nonneg_left ((nrm_sub_abs _ _).trans hn2) (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- **Lemma SA, concentration.** If `z_F` is `L`-Lipschitz, then for `u ≥ 0`:
`Pr_η(T_s ≥ E_η T_s + u) ≤ exp(−2u²/(π²·ℓ_s²))`, `ℓ_s = √(t_F)·L·|σ|/√k`. (The fact (G1) of the
document has `exp(−u²/(2ℓ_s²))`; Lean has the constant of Part 148.) -/
theorem lemmaSA_conc (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) {L : ℝ}
    (hL0 : 0 ≤ L)
    (hL : ∀ y y', normSq (hid2 θ.1 θ.2 y - hid2 θ.1 θ.2 y') ≤ L ^ 2 * normSq (y - y'))
    {u : ℝ} (hu : 0 ≤ u) :
    (gamK k n).real {η | ∫ η, Ts θ c σ k η ∂gamK k n + u ≤ Ts θ c σ k η} ≤
      Real.exp (-2 * u ^ 2 / (Real.pi ^ 2 * (√(2 / (m : ℝ)) * L * |σ| / √(k : ℝ)) ^ 2)) := by
  have hℓ0 : 0 ≤ √(2 / (m : ℝ)) * L * |σ| / √(k : ℝ) := by positivity
  have h := BstLean.Part148.gaussConc_mat_upper (m := k) (k := n)
    (g := fun M : Matrix (Fin k) (Fin n) ℝ => Ts θ c σ k M) hℓ0
    (fun M M' => lemmaSA_lip θ c σ hk hL0 hL M M') (v := 1) (by norm_num) hu
  rw [one_mul, ← gamK_eq_gaussMat] at h
  exact h

lemma measurable_Ts (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) (k : ℕ) :
    Measurable (Ts θ c σ k) := by
  have hz := continuous_zS θ c σ
  have hd : ∀ i : Fin m, Measurable (fun η : Fin k → Fin n → ℝ => dSamp θ c σ k η i) := by
    intro i
    unfold dSamp
    refine (measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)).sub measurable_const
    exact ((continuous_apply i).comp hz).measurable.comp (measurable_pi_apply j)
  unfold Ts normSq
  exact (measurable_const.mul (Finset.measurable_sum _ fun i _ => (hd i).pow_const 2)).sqrt

/-- `E_η T_s ≤ √(t_F·E_γ|z_F(c + σγ)|²/k)`. -/
theorem Ts_mean_le (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∫ η, Ts θ c σ k η ∂gamK k n ≤
      √(2 / (m : ℝ) * ((∫ γ, normSq (zS θ c σ γ) ∂stdGauss (Fin n)) / k)) := by
  obtain ⟨hI, hle⟩ := lemmaSA_fixed_int θ c σ hk
  have hsq : ∀ η : Fin k → Fin n → ℝ, Ts θ c σ k η ^ 2 = 2 / (m : ℝ) * normSq (dSamp θ c σ k η) :=
    fun η => Real.sq_sqrt (mul_nonneg (by positivity) (normSq_nonneg _))
  have hI2 : Integrable (fun η : Fin k → Fin n → ℝ => Ts θ c σ k η ^ 2) (gamK k n) := by
    simp_rw [hsq]; exact hI.const_mul _
  have h1 := BstLean.Part133.sq_integral_le (ρ := gamK k n) hI2
  have h2 : ∫ η, Ts θ c σ k η ^ 2 ∂gamK k n ≤
      2 / (m : ℝ) * ((∫ γ, normSq (zS θ c σ γ) ∂stdGauss (Fin n)) / k) := by
    simp_rw [hsq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  exact Real.le_sqrt_of_sq_le (h1.trans h2)

/-- **Lemma SA, concentration around the root of the second moment.** If `z_F` is
`L`-Lipschitz, then for `u ≥ 0`, except with probability `exp(−2u²/(π²·ℓ_s²))` over `η`:
`T_s < √(t_F·E_γ|z_F(c + σγ)|²/k) + u`. -/
theorem lemmaSA_conc' (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) {L : ℝ}
    (hL0 : 0 ≤ L)
    (hL : ∀ y y', normSq (hid2 θ.1 θ.2 y - hid2 θ.1 θ.2 y') ≤ L ^ 2 * normSq (y - y'))
    {u : ℝ} (hu : 0 ≤ u) :
    (gamK k n).real {η | √(2 / (m : ℝ) *
        ((∫ γ, normSq (zS θ c σ γ) ∂stdGauss (Fin n)) / k)) + u ≤ Ts θ c σ k η} ≤
      Real.exp (-2 * u ^ 2 / (Real.pi ^ 2 * (√(2 / (m : ℝ)) * L * |σ| / √(k : ℝ)) ^ 2)) := by
  refine le_trans (measureReal_mono ?_) (lemmaSA_conc θ c σ hk hL0 hL hu)
  intro η hη
  simp only [mem_ofPred_eq] at hη ⊢
  have := Ts_mean_le θ c σ hk
  linarith

end BstLean.Part151
