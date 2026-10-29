import BstLean.Part149SDefs

/-!
# Part 149, item 5: the sample output of the program with the mean-field centre, the sampling error

Do not use `sorry`, `native_decide` or `axiom`.

* `iid_mean_sq_L2`: for a square-integrable `f` and `k ≥ 1` independent points,
  `E(k⁻¹·Σ_i f(x_i) − E f)² ≤ E f²/k` (the form of `Part139.iid_mean_sq` without boundedness).
* `measurable_gSampB`: the sample output is jointly measurable.
* `sampB_second`: `E_{A₃, F, γ} F(A₃ b + τ·γ)² = 4/n` if `|b|² ≤ m/n`, `τ = tauOutOf n b`.
* **`sampB_lint`**: `E[1_X(W, A₁, A₂)·(gSampB − gOutB)²] ≤ 4/n/k`, the mean over `(W, A, F)` and the
  `k` Gaussian vectors, for a measurable set `X` on which `|bMF|² ≤ m_A/n`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part141

/-! ## The mean of `k` independent values of a square-integrable function -/

/-- **The second moment of a sample mean around the mean.** For a probability measure `ν`, a
measurable square-integrable `f` and `k ≥ 1` independent points:
`E(k⁻¹·Σ_i f(x_i) − E f)² ≤ k⁻¹·E f²`. -/
lemma iid_mean_sq_L2 {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    {f : X → ℝ} (hm : Measurable f) (hf : MemLp f 2 ν) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ x : Fin k → X, ENNReal.ofReal (((k : ℝ)⁻¹ * ∑ i, f (x i) - ∫ x, f x ∂ν) ^ 2)
        ∂Measure.pi (fun _ : Fin k => ν) ≤
      ENNReal.ofReal ((k : ℝ)⁻¹) * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν := by
  set π := Measure.pi fun _ : Fin k => ν with hπ
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : ∀ i : Fin k, MemLp (fun x : Fin k → X => f (x i)) 2 π := fun i =>
    hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin k => ν) i)
  set Sf : (Fin k → X) → ℝ := fun x => ∑ i, f (x i) with hSf
  have hS : MemLp Sf 2 π := memLp_finsetSum _ fun i _ => hc i
  have hY : MemLp (fun x : Fin k → X => (k : ℝ)⁻¹ * Sf x) 2 π := hS.const_mul _
  have hmean1 : ∀ i : Fin k, ∫ x : Fin k → X, f (x i) ∂π = ∫ x, f x ∂ν := by
    intro i
    have h := integral_map (μ := π) (φ := Function.eval i)
      (measurable_pi_apply i).aemeasurable (f := f)
      (by rw [(measurePreserving_eval (fun _ : Fin k => ν) i).map_eq]
          exact hm.aestronglyMeasurable)
    rw [(measurePreserving_eval (fun _ : Fin k => ν) i).map_eq] at h
    exact h.symm
  have hmean : ∫ x, (k : ℝ)⁻¹ * Sf x ∂π = ∫ x, f x ∂ν := by
    rw [integral_const_mul, hSf,
      integral_finsetSum _ fun i _ => (hc i).integrable one_le_two]
    simp_rw [hmean1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hvar : Var[fun x : Fin k → X => (k : ℝ)⁻¹ * Sf x; π] = (k : ℝ)⁻¹ * Var[f; ν] := by
    rw [variance_const_mul]
    have h := variance_sum_pi (μ := fun _ : Fin k => ν) (X := fun _ : Fin k => f)
      (fun _ => hf)
    have e : (∑ i : Fin k, fun ω : Fin k → X => f (ω i)) = Sf := by
      funext ω
      simp [hSf, Finset.sum_apply]
    rw [e] at h
    rw [h]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hv2 := variance_eq_integral (μ := π) hY.aestronglyMeasurable.aemeasurable
  rw [hmean, hvar] at hv2
  have hi : Integrable (fun x : Fin k → X => ((k : ℝ)⁻¹ * Sf x - ∫ x, f x ∂ν) ^ 2) π :=
    (hY.sub (memLp_const _)).integrable_sq
  have hle : Var[f; ν] ≤ ∫ x, f x ^ 2 ∂ν := variance_le_expectation_sq hm.aestronglyMeasurable
  have i0 : 0 ≤ ∫ x, f x ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
      (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ← ENNReal.ofReal_mul (by positivity), ← hv2]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hle (by positivity))

/-! ## Measurability -/

section meas

variable {n : ℕ}

lemma measurable_bMFW :
    Measurable (fun q : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n => bMFW q.1 q.2) := by
  have hX : Measurable (fun q : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n =>
      ((cenA q.1, tauWA q.1), thA q.2)) :=
    ((measurable_cenA.comp measurable_fst).prodMk (measurable_tauWA.comp measurable_fst)).prodMk
      (measurable_thA.comp measurable_snd)
  have h2 := (measurable_bMF (n := n) (m := mA n)).comp hX
  simp only [Function.comp_def] at h2
  exact h2

lemma measurable_preB :
    Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) × (Fin n → ℝ) =>
      preB q.1.1 q.1.2 q.2) := by
  unfold preB
  have hb : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) ×
      (Fin n → ℝ) => bMFW q.1.1 q.1.2) := by
    have hf : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) ×
        (Fin n → ℝ) => q.1) := measurable_fst
    have h := (measurable_bMFW (n := n)).comp hf
    simp only [Function.comp_def] at h
    exact h
  have hA : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) ×
      (Fin n → ℝ) => q.1.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hmv := (BstLean.Part134.measurable_mulVec_joint (n := n) (m := mA n)).comp (hA.prodMk hb)
  simp only [Function.comp_def] at hmv
  have hτ := (measurable_tauOutOf (n := n) (m := mA n)).comp hb
  simp only [Function.comp_def] at hτ
  exact hmv.add (hτ.smul measurable_snd)

lemma measurable_preB_WA (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n) :
    Measurable (preB W A) := by
  unfold preB
  exact measurable_const.add (measurable_const_smul _)

lemma measurable_gSampB (k : ℕ) :
    Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ) => gSampB k p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold gSampB
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  have h0 : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => ((p.1.1, p.1.2.1), p.2 i)) :=
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  have h1 := (measurable_preB (n := n)).comp h0
  simp only [Function.comp_def] at h1
  exact measurable_evF_comp (measurable_snd.comp (measurable_snd.comp measurable_fst)) h1

end meas

/-! ## The second moment of one point -/

section second

variable {n m mF : ℕ}

/-- `E_F F(y)² = 2|y|²/n`, as a lower integral. -/
lemma lint_evF_sq (hmF : 1 ≤ mF) (y : Fin n → ℝ) :
    ∫⁻ F : MlpParam n mF 1, ENNReal.ofReal (evF F y ^ 2) ∂mlpGauss n mF 1 =
      ENNReal.ofReal (2 * normSq y / n) := by
  have e : ∀ F : MlpParam n mF 1, evF F y ^ 2 = normSq (mlpEval F y) := by
    intro F
    simp [normSq, evF]
  have hi : Integrable (fun F : MlpParam n mF 1 => evF F y ^ 2) (mlpGauss n mF 1) := by
    simp_rw [e]
    exact mlp_normSq_integrable y
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  congr 1
  exact F_second_moment hmF y

/-- **The second moment of one sample point**: if `|b|² ≤ m/n` and `τ = tauOutOf n b`, then
`E_{A₃, F, γ} F(A₃ b + τ·γ)² = 4/n`. -/
lemma sampB_second (hn : 1 ≤ n) (hm : 1 ≤ m) (hmF : 1 ≤ mF) {b : Fin m → ℝ}
    (hb : normSq b ≤ (m : ℝ) / n) :
    ∫⁻ y : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1,
        ∫⁻ γ, ENNReal.ofReal (evF y.2 (y.1.mulVec b + tauOutOf n b • γ) ^ 2) ∂stdGauss (Fin n)
        ∂((gaussMat n m (2 / (m : ℝ))).prod (mlpGauss n mF 1)) = ENNReal.ofReal (4 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set τ : ℝ := tauOutOf n b with hτ
  have hτ2 : τ ^ 2 = 2 / (n : ℝ) - 2 / (m : ℝ) * normSq b := by
    have h0 : 0 ≤ 2 / (n : ℝ) - 2 / (m : ℝ) * normSq b := by
      have : 2 / (m : ℝ) * normSq b ≤ 2 / (m : ℝ) * ((m : ℝ) / n) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      have e : 2 / (m : ℝ) * ((m : ℝ) / n) = 2 / (n : ℝ) := by field_simp
      linarith
    rw [hτ]
    unfold tauOutOf
    rw [Real.sq_sqrt (le_max_left _ _), max_eq_right h0]
  clear_value τ
  have mpt : Measurable (fun q : (Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1) × (Fin n → ℝ) =>
      q.1.1.mulVec b + τ • q.2) := by
    have hf : Measurable (fun q : (Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1) × (Fin n → ℝ) =>
        (q.1.1, b)) := (measurable_fst.comp measurable_fst).prodMk measurable_const
    have h := (BstLean.Part134.measurable_mulVec_joint (n := n) (m := m)).comp hf
    simp only [Function.comp_def] at h
    exact h.add (measurable_snd.const_smul τ)
  have mg : Measurable (fun q : (Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1) × (Fin n → ℝ) =>
      ENNReal.ofReal (evF q.1.2 (q.1.1.mulVec b + τ • q.2) ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_evF_comp (measurable_snd.comp measurable_fst) mpt).pow_const 2)
  rw [lintegral_prod _ mg.lintegral_prod_right'.aemeasurable]
  have key : ∀ M : Matrix (Fin n) (Fin m) ℝ,
      ∫⁻ F : MlpParam n mF 1, ∫⁻ γ, ENNReal.ofReal (evF F (M.mulVec b + τ • γ) ^ 2)
          ∂stdGauss (Fin n) ∂mlpGauss n mF 1 =
        ENNReal.ofReal (2 / (n : ℝ) * (normSq (M.mulVec b) + τ ^ 2 * n)) := by
    intro M
    have mgM : Measurable (fun q : MlpParam n mF 1 × (Fin n → ℝ) =>
        ENNReal.ofReal (evF q.1 (M.mulVec b + τ • q.2) ^ 2)) := by
      have hf : Measurable (fun q : MlpParam n mF 1 × (Fin n → ℝ) => ((M, q.1), q.2)) :=
        (measurable_const.prodMk measurable_fst).prodMk measurable_snd
      have h := mg.comp hf
      simp only [Function.comp_def] at h
      exact h
    rw [lintegral_lintegral_swap mgM.aemeasurable]
    simp_rw [lint_evF_sq hmF]
    obtain ⟨hgi, hge⟩ := gauss_shift_normSq (M.mulVec b) τ
    have hi : Integrable (fun γ : Fin n → ℝ => 2 * normSq (M.mulVec b + τ • γ) / n)
        (stdGauss (Fin n)) := (hgi.const_mul 2).div_const _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun γ => by
      have := normSq_nonneg (M.mulVec b + τ • γ)
      positivity)]
    congr 1
    rw [integral_div, integral_const_mul, hge]
    ring
  simp_rw [key]
  obtain ⟨iM, eM⟩ := layer_lin_sq (m := n) (k := m) (two_div_nonneg m) b
  have iR : Integrable (fun M : Matrix (Fin n) (Fin m) ℝ =>
      2 / (n : ℝ) * (normSq (M.mulVec b) + τ ^ 2 * n)) (gaussMat n m (2 / (m : ℝ))) :=
    (iM.add (integrable_const _)).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal iR (Filter.Eventually.of_forall fun M => by
    have := normSq_nonneg (M.mulVec b)
    positivity)]
  congr 1
  rw [integral_const_mul, integral_add iM (integrable_const _), eM]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [hτ2]
  field_simp
  ring

end second

/-! ## The sampling error -/

section joint

variable {n : ℕ}

/-- The function `γ ↦ F(preB W A γ)` is square-integrable. -/
lemma memLp_evF_preB {mF : ℕ} (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (F : MlpParam n mF 1) :
    MemLp (fun γ : Fin n → ℝ => evF F (preB W A γ)) 2 (stdGauss (Fin n)) := by
  have hmeas : Measurable (fun γ : Fin n → ℝ => evF F (preB W A γ)) :=
    (measurable_evF F).comp (measurable_preB_WA W A)
  rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
  obtain ⟨C, hC0, hC⟩ := evF_growth F
  have hg := (gauss_shift_normSq (A.2.2.mulVec (bMFW W A)) (tauOutOf n (bMFW W A))).1
  have iG : Integrable (fun γ : Fin n → ℝ => C * (1 + normSq (preB W A γ))) (stdGauss (Fin n)) :=
    ((integrable_const (1 : ℝ)).add hg).const_mul C
  refine Integrable.mono' iG (hmeas.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun γ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hC _

/-- The second moment of one point of the sample, on the set `X`. -/
noncomputable def LsB (X : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n)))
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) : ℝ≥0∞ :=
  ({t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      (t.1, thA t.2.1) ∈ X}).indicator
    (fun t => ∫⁻ γ, ENNReal.ofReal (evF t.2.2 (preB t.1 t.2.1 γ) ^ 2) ∂stdGauss (Fin n)) t

lemma measurable_LsB {X : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))}
    (hX : MeasurableSet X) : Measurable (LsB X) := by
  unfold LsB
  have hj : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin n → ℝ) =>
      ENNReal.ofReal (evF q.1.2.2 (preB q.1.1 q.1.2.1 q.2) ^ 2)) := by
    have h0 : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin n → ℝ) => ((q.1.1, q.1.2.1), q.2)) :=
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd
    have h1 := (measurable_preB (n := n)).comp h0
    simp only [Function.comp_def] at h1
    exact ENNReal.measurable_ofReal.comp ((measurable_evF_comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst)) h1).pow_const 2)
  refine hj.lintegral_prod_right'.indicator ?_
  exact (measurable_fst.prodMk (measurable_thA.comp (measurable_fst.comp measurable_snd))) hX

/-- `E[LsB] ≤ 4/n`. -/
lemma lint_LsB (hn : 1 ≤ n) {X : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))}
    (hX : MeasurableSet X)
    (hb : ∀ x ∈ X, normSq (bMF (cenA x.1) (tauWA x.1) x.2) ≤ (mA n : ℝ) / n) :
    ∫⁻ t, LsB X t ∂mlpTriple 2 n ≤ ENNReal.ofReal (4 / (n : ℝ)) := by
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by
    unfold mF
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnR _)).ne'
  have mL := measurable_LsB hX
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  rw [e0, lintegral_prod _ mL.aemeasurable]
  have inner : ∀ W : MlpParam (2 * n) (mW n) n,
      ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1, LsB X (W, p)
          ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤ ENNReal.ofReal (4 / (n : ℝ)) := by
    intro W
    have mgW : Measurable (fun p : MlpParam n (mA n) n × MlpParam n (mF n) 1 => LsB X (W, p)) :=
      mL.comp measurable_prodMk_left
    have h4 := lint_assoc4 (gaussMat (mA n) n (2 / (n : ℝ)))
      (gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) (gaussMat n (mA n) (2 / (mA n : ℝ)))
      (mlpGauss n (mF n) 1) mgW
    have e1 : (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) =
        ((gaussMat (mA n) n (2 / (n : ℝ))).prod ((gaussMat (mA n) (mA n) (2 / (mA n : ℝ))).prod
          (gaussMat n (mA n) (2 / (mA n : ℝ))))).prod (mlpGauss n (mF n) 1) := rfl
    rw [e1, h4]
    have each : ∀ θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
        ∫⁻ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
          LsB X (W, (θ.1, θ.2, y.1), y.2)
          ∂((gaussMat n (mA n) (2 / (mA n : ℝ))).prod (mlpGauss n (mF n) 1)) ≤
        ENNReal.ofReal (4 / (n : ℝ)) := by
      intro θ
      by_cases hx : ((W, θ) : MlpParam (2 * n) (mW n) n × HidParam n (mA n)) ∈ X
      · have e : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
            LsB X (W, (θ.1, θ.2, y.1), y.2) =
              ∫⁻ γ, ENNReal.ofReal (evF y.2 (y.1.mulVec (bMF (cenA W) (tauWA W) θ) +
                tauOutOf n (bMF (cenA W) (tauWA W) θ) • γ) ^ 2) ∂stdGauss (Fin n) := by
          intro y
          unfold LsB
          rw [Set.indicator_of_mem (show ((W, (θ.1, θ.2, y.1), y.2) : MlpParam (2 * n) (mW n) n ×
            MlpParam n (mA n) n × MlpParam n (mF n) 1) ∈ {t : MlpParam (2 * n) (mW n) n ×
              MlpParam n (mA n) n × MlpParam n (mF n) 1 | (t.1, thA t.2.1) ∈ X} from hx)]
          rfl
        simp_rw [e]
        have hbx : normSq (bMF (cenA W) (tauWA W) θ) ≤ (mA n : ℝ) / n := hb (W, θ) hx
        have h := sampB_second (n := n) (m := mA n) (mF := mF n) hn hmA hmF
          (b := bMF (cenA W) (tauWA W) θ) hbx
        exact le_of_eq h
      · have e : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
            LsB X (W, (θ.1, θ.2, y.1), y.2) = 0 := by
          intro y
          unfold LsB
          rw [Set.indicator_of_notMem (show ((W, (θ.1, θ.2, y.1), y.2) :
            MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ∉
              {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
                (t.1, thA t.2.1) ∈ X} from hx)]
        simp_rw [e]
        simp
    refine (lintegral_mono each).trans ?_
    simp
  refine (lintegral_mono inner).trans ?_
  simp

/-- **The sampling error of the program with the mean-field centre.** For `n ≥ 1`, `k ≥ 1` and a
measurable set `X` of `(W, (A₁, A₂))` on which `|bMF|² ≤ m_A/n`:
`E[1_X·(gSampB − gOutB)²] ≤ 4/n/k`, the mean over `(W, A, F)` and the `k` Gaussian vectors. -/
theorem sampB_lint {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    {X : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (hX : MeasurableSet X)
    (hb : ∀ x ∈ X, normSq (bMF (cenA x.1) (tauWA x.1) x.2) ≤ (mA n : ℝ) / n) :
    ∫⁻ p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ),
      ENNReal.ofReal (({p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X}).indicator
        (fun p => (gSampB k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutB p.1.1 p.1.2.1 p.1.2.2) ^ 2) p)
      ∂((mlpTriple 2 n).prod (gamK k n)) ≤ ENNReal.ofReal (4 / (n : ℝ) / k) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have mT : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X} :=
    ((measurable_fst.comp measurable_fst).prodMk (measurable_thA.comp
      (measurable_fst.comp (measurable_snd.comp measurable_fst)))) hX
  have mf : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) =>
      ENNReal.ofReal (({p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X}).indicator
        (fun p => (gSampB k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutB p.1.1 p.1.2.1 p.1.2.2) ^ 2) p)) :=
    ENNReal.measurable_ofReal.comp ((((measurable_gSampB k).sub
      (measurable_gOutB.comp measurable_fst)).pow_const 2).indicator mT)
  rw [lintegral_prod _ mf.aemeasurable]
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ∫⁻ γ, ENNReal.ofReal (({p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X}).indicator
        (fun p => (gSampB k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutB p.1.1 p.1.2.1 p.1.2.2) ^ 2) (t, γ))
        ∂gamK k n ≤ ENNReal.ofReal ((k : ℝ)⁻¹) * LsB X t := by
    rintro ⟨W, A, F⟩
    by_cases hx : ((W, thA A) : MlpParam (2 * n) (mW n) n × HidParam n (mA n)) ∈ X
    · have e1 : ∀ γ : Fin k → Fin n → ℝ,
          ({p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
            MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X}).indicator
          (fun p => (gSampB k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutB p.1.1 p.1.2.1 p.1.2.2) ^ 2)
          ((W, A, F), γ) = ((k : ℝ)⁻¹ * ∑ i, evF F (preB W A (γ i)) -
            ∫ γ, evF F (preB W A γ) ∂stdGauss (Fin n)) ^ 2 := by
        intro γ
        rw [Set.indicator_of_mem (show (((W, A, F), γ) : (MlpParam (2 * n) (mW n) n ×
          MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ)) ∈
            {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
              MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X} from hx)]
        rfl
      simp_rw [e1]
      have e2 : LsB X (W, A, F) =
          ∫⁻ γ, ENNReal.ofReal (evF F (preB W A γ) ^ 2) ∂stdGauss (Fin n) := by
        unfold LsB
        rw [Set.indicator_of_mem (show ((W, A, F) : MlpParam (2 * n) (mW n) n ×
          MlpParam n (mA n) n × MlpParam n (mF n) 1) ∈ {t : MlpParam (2 * n) (mW n) n ×
            MlpParam n (mA n) n × MlpParam n (mF n) 1 | (t.1, thA t.2.1) ∈ X} from hx)]
      rw [e2]
      exact iid_mean_sq_L2 (stdGauss (Fin n))
        ((measurable_evF F).comp (measurable_preB_WA W A)) (memLp_evF_preB W A F) hk
    · have e1 : ∀ γ : Fin k → Fin n → ℝ,
          ({p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
            MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X}).indicator
          (fun p => (gSampB k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutB p.1.1 p.1.2.1 p.1.2.2) ^ 2)
          ((W, A, F), γ) = 0 := by
        intro γ
        rw [Set.indicator_of_notMem (show (((W, A, F), γ) : (MlpParam (2 * n) (mW n) n ×
          MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ)) ∉
            {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
              MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X} from hx)]
      simp_rw [e1]
      simp
  refine (lintegral_mono key).trans ?_
  rw [lintegral_const_mul _ (measurable_LsB hX)]
  refine (mul_le_mul' le_rfl (lint_LsB hn hX hb)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end joint

end BstLean.Part149

open BstLean.Part149 in
#print axioms iid_mean_sq_L2
open BstLean.Part149 in
#print axioms measurable_gSampB
open BstLean.Part149 in
#print axioms sampB_second
open BstLean.Part149 in
#print axioms sampB_lint
