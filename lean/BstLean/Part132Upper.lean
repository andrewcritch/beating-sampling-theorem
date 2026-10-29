import BstLean.Part132Agent
import BstLean.Part132Cos
import BstLean.Part132Rows

/-!
# Part 132, item 3 (tools): upper bounds through the hidden layers of `F`

Role: `delegations/statements/p132-spec.md`. Paper source: `onW2c-cx.md` §3 ((6), (7): the
two-point bound with absolute error `c₀/√m_1`); `onW4c-cx.md` §3 ("Upper bound of b₁₁").

* `integral_abs_le_sqrt`: `E|f| ≤ √(E f²)`.
* `relu_layer_upper`: `E Ψ_G(ReLU(Mh), ReLU(Mh′)) ≤ (m/2)v·[Ψ_{G∘κ}(h, h′) + ((√6 + 2√5·G(0))/√m)|h||h′|]`
  (the Lipschitz bound of the perspective; `Var ĉ ≤ 6σ²σ′²/m` from the independent rows).
* `integral_mul_le_sqrt` (Cauchy–Schwarz), `norm_pair_abs`, `relu_layer_pair_abs`.
* `KF_upper`: `E_F (2/m_F)⟨H(y), H(y′)⟩ ≤ (2/n)·[Ψ_{κ∘κ}(y, y′) + ((√6 + 2√5·κ(0))/√m_F)|y||y′|]`:
  the paper constant `c₀ = √6 + 2√5/π`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131

/-- `E|f| ≤ √(E f²)` under a probability measure. -/
theorem integral_abs_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (hf2 : Integrable (fun ω => f ω ^ 2) μ) :
    Integrable (fun ω => |f ω|) μ ∧ ∫ ω, |f ω| ∂μ ≤ √(∫ ω, f ω ^ 2 ∂μ) := by
  have habs : Integrable (fun ω => |f ω|) μ :=
    integrable_of_sq hf.abs (fun ω => abs_nonneg _) (by simp_rw [sq_abs]; exact hf2)
  refine ⟨habs, ?_⟩
  set c := ∫ ω, |f ω| ∂μ with hc
  obtain ⟨iR, eR⟩ := integral_lin4 (μ := μ) hf2 habs habs habs (c ^ 2) 1 (2 * c) 0 0
  have h0 : 0 ≤ ∫ ω, (1 * f ω ^ 2 + c ^ 2 - 2 * c * |f ω| - 0 * |f ω| - 0 * |f ω|) ∂μ := by
    refine integral_nonneg fun ω => ?_
    have : 1 * f ω ^ 2 + c ^ 2 - 2 * c * |f ω| - 0 * |f ω| - 0 * |f ω| = (|f ω| - c) ^ 2 := by
      rw [← sq_abs (f ω)]; ring
    rw [this]; positivity
  rw [eR, ← hc] at h0
  have h1 : c ^ 2 ≤ ∫ ω, f ω ^ 2 ∂μ := by nlinarith
  exact (le_abs_self c).trans (Real.abs_le_sqrt h1)

/-- Cauchy–Schwarz: `E|UV| ≤ √(E U²)·√(E V²)` under a probability measure. -/
theorem integral_mul_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {U V : Ω → ℝ} (hU : Measurable U) (hV : Measurable V)
    (hU2 : Integrable (fun ω => U ω ^ 2) μ) (hV2 : Integrable (fun ω => V ω ^ 2) μ) :
    Integrable (fun ω => |U ω| * |V ω|) μ ∧
    ∫ ω, |U ω| * |V ω| ∂μ ≤ √(∫ ω, U ω ^ 2 ∂μ) * √(∫ ω, V ω ^ 2 ∂μ) := by
  have hi : Integrable (fun ω => |U ω| * |V ω|) μ := by
    refine Integrable.mono' ((hU2.add hV2).div_const 2) (hU.abs.mul hV.abs).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (|U ω| - |V ω|), sq_abs (U ω), sq_abs (V ω)]
  refine ⟨hi, ?_⟩
  set I := ∫ ω, |U ω| * |V ω| ∂μ with hI
  set P := ∫ ω, U ω ^ 2 ∂μ with hP
  set Q := ∫ ω, V ω ^ 2 ∂μ with hQ
  have hI0 : 0 ≤ I := integral_nonneg fun ω => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hP0 : 0 ≤ P := integral_nonneg fun ω => sq_nonneg _
  have hQ0 : 0 ≤ Q := integral_nonneg fun ω => sq_nonneg _
  -- for every `l`: `0 ≤ l²P − 2lI + Q`
  have hq : ∀ l : ℝ, 0 ≤ l ^ 2 * P + Q - 2 * l * I := by
    intro l
    obtain ⟨iR, eR⟩ := integral_lin4 (μ := μ) hU2 hV2 hi hi 0 (l ^ 2) (-1) (2 * l) 0
    have h0 : 0 ≤ ∫ ω, (l ^ 2 * U ω ^ 2 + 0 - -1 * V ω ^ 2 - 2 * l * (|U ω| * |V ω|) -
        0 * (|U ω| * |V ω|)) ∂μ := by
      refine integral_nonneg fun ω => ?_
      have : l ^ 2 * U ω ^ 2 + 0 - -1 * V ω ^ 2 - 2 * l * (|U ω| * |V ω|) -
          0 * (|U ω| * |V ω|) = (l * |U ω| - |V ω|) ^ 2 := by
        rw [← sq_abs (U ω), ← sq_abs (V ω)]; ring
      rw [this]; positivity
    rw [eR] at h0
    linarith
  have key : I ^ 2 ≤ P * Q := by
    rcases eq_or_lt_of_le hP0 with h | h
    · have hI' : I = 0 := by
        by_contra hne
        have hpos : 0 < I := lt_of_le_of_ne hI0 (Ne.symm hne)
        have h1 := hq ((Q + 1) / (2 * I))
        rw [← h] at h1
        have e : ((Q + 1) / (2 * I)) ^ 2 * 0 + Q - 2 * ((Q + 1) / (2 * I)) * I = -1 := by
          field_simp; ring
        rw [e] at h1
        linarith
      rw [hI', ← h]; simp
    · have h1 := hq (I / P)
      have e : (I / P) ^ 2 * P + Q - 2 * (I / P) * I = Q - I ^ 2 / P := by
        field_simp; ring
      rw [e] at h1
      have h2 : I ^ 2 / P ≤ Q := by linarith
      rw [div_le_iff₀ h] at h2
      linarith
  rw [← Real.sqrt_mul hP0]
  exact (le_abs_self I).trans (Real.abs_le_sqrt key)

/-- The first absolute moment in `norm_pair`: `E|√X√Y − αβ| ≤ 2√ε·αβ` (paper: onW2c §3,
`E|α̂β̂ − σσ′| ≤ 2σσ′√(5/m_1)`). -/
theorem norm_pair_abs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω) (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    (hY2 : Integrable (fun ω => Y ω ^ 2) μ) {α β ε : ℝ} (hα : 0 < α) (hβ : 0 < β) (hε : 0 ≤ ε)
    (hEX : ∫ ω, X ω ∂μ = α ^ 2) (hEY : ∫ ω, Y ω ∂μ = β ^ 2)
    (hEX2 : ∫ ω, X ω ^ 2 ∂μ ≤ (1 + ε) * α ^ 4) (hEY2 : ∫ ω, Y ω ^ 2 ∂μ ≤ (1 + ε) * β ^ 4) :
    Integrable (fun ω => |√(X ω) * √(Y ω) - α * β|) μ ∧
    ∫ ω, |√(X ω) * √(Y ω) - α * β| ∂μ ≤ 2 * √ε * (α * β) := by
  have hXi := integrable_of_sq hX hX0 hX2
  have hYi := integrable_of_sq hY hY0 hY2
  -- `E(√X − α)² ≤ ε α²`
  have dev : ∀ {Z : Ω → ℝ} {γ : ℝ}, Measurable Z → (∀ ω, 0 ≤ Z ω) →
      Integrable (fun ω => Z ω ^ 2) μ → Integrable Z μ → 0 < γ → ∫ ω, Z ω ∂μ = γ ^ 2 →
      ∫ ω, Z ω ^ 2 ∂μ ≤ (1 + ε) * γ ^ 4 →
      Integrable (fun ω => (√(Z ω) - γ) ^ 2) μ ∧ ∫ ω, (√(Z ω) - γ) ^ 2 ∂μ ≤ ε * γ ^ 2 := by
    intro Z γ hZ hZ0 hZ2 hZi hγ hEZ hEZ2
    obtain ⟨iR, eR⟩ := integral_lin4 (μ := μ) hZ2 hZi hZi hZi (γ ^ 2) (1 / γ ^ 2) 2 0 0
    have hpt : ∀ ω, (√(Z ω) - γ) ^ 2 ≤
        1 / γ ^ 2 * Z ω ^ 2 + γ ^ 2 - 2 * Z ω - 0 * Z ω - 0 * Z ω := by
      intro ω
      have e : 1 / γ ^ 2 * Z ω ^ 2 + γ ^ 2 - 2 * Z ω - 0 * Z ω - 0 * Z ω =
          (Z ω - γ ^ 2) ^ 2 / γ ^ 2 := by field_simp; ring
      rw [e, le_div_iff₀ (by positivity)]
      have hs := Real.sq_sqrt (hZ0 ω)
      have hs0 := Real.sqrt_nonneg (Z ω)
      have e2 : Z ω - γ ^ 2 = (√(Z ω) - γ) * (√(Z ω) + γ) := by nlinarith
      rw [e2, mul_pow]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
    have hint : Integrable (fun ω => (√(Z ω) - γ) ^ 2) μ := by
      refine Integrable.mono' iR ((hZ.sqrt.sub measurable_const).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpt ω
    refine ⟨hint, ?_⟩
    have h := integral_mono hint iR hpt
    rw [eR, hEZ] at h
    refine h.trans ?_
    have h2 := mul_le_mul_of_nonneg_left hEZ2 (by positivity : (0 : ℝ) ≤ 1 / γ ^ 2)
    have e3 : 1 / γ ^ 2 * ((1 + ε) * γ ^ 4) = (1 + ε) * γ ^ 2 := by field_simp
    rw [e3] at h2
    nlinarith
  obtain ⟨iA, uA⟩ := dev hX hX0 hX2 hXi hα hEX hEX2
  obtain ⟨iB, uB⟩ := dev hY hY0 hY2 hYi hβ hEY hEY2
  have hY' : Integrable (fun ω => √(Y ω) ^ 2) μ := by
    have : (fun ω => √(Y ω) ^ 2) = Y := funext fun ω => Real.sq_sqrt (hY0 ω)
    rw [this]; exact hYi
  obtain ⟨i1, u1⟩ := integral_mul_le_sqrt (μ := μ) (U := fun ω => √(X ω) - α)
    (V := fun ω => √(Y ω)) (hX.sqrt.sub measurable_const) hY.sqrt iA hY'
  obtain ⟨i2, u2⟩ := integral_abs_le_sqrt (μ := μ) (f := fun ω => √(Y ω) - β)
    (hY.sqrt.sub measurable_const) iB
  have hbnd : Integrable (fun ω => |√(X ω) - α| * |√(Y ω)| + α * |√(Y ω) - β|) μ :=
    i1.add (i2.const_mul α)
  have hpt : ∀ ω, |√(X ω) * √(Y ω) - α * β| ≤ |√(X ω) - α| * |√(Y ω)| + α * |√(Y ω) - β| := by
    intro ω
    have e : √(X ω) * √(Y ω) - α * β = (√(X ω) - α) * √(Y ω) + α * (√(Y ω) - β) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hα]
  have hmeas : Measurable (fun ω => |√(X ω) * √(Y ω) - α * β|) :=
    ((hX.sqrt.mul hY.sqrt).sub measurable_const).abs
  have hint : Integrable (fun ω => |√(X ω) * √(Y ω) - α * β|) μ := by
    refine Integrable.mono' hbnd hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact hpt ω
  refine ⟨hint, ?_⟩
  have h := integral_mono hint hbnd hpt
  have a1 := integral_add i1 (i2.const_mul α)
  have a2 : ∫ ω, α * |√(Y ω) - β| ∂μ = α * ∫ ω, |√(Y ω) - β| ∂μ := integral_const_mul _ _
  beta_reduce at a1
  rw [a1, a2] at h
  refine h.trans ?_
  have eY : ∫ ω, √(Y ω) ^ 2 ∂μ = β ^ 2 := by
    have : (fun ω => √(Y ω) ^ 2) = Y := funext fun ω => Real.sq_sqrt (hY0 ω)
    rw [this]; exact hEY
  rw [eY, Real.sqrt_sq hβ.le] at u1
  have s1 : √(∫ ω, (√(X ω) - α) ^ 2 ∂μ) ≤ √ε * α := by
    have := Real.sqrt_le_sqrt uA
    rwa [Real.sqrt_mul hε, Real.sqrt_sq hα.le] at this
  have s2 : √(∫ ω, (√(Y ω) - β) ^ 2 ∂μ) ≤ √ε * β := by
    have := Real.sqrt_le_sqrt uB
    rwa [Real.sqrt_mul hε, Real.sqrt_sq hβ.le] at this
  have t1 := u1.trans (mul_le_mul_of_nonneg_right s1 hβ.le)
  have t2 := mul_le_mul_of_nonneg_left (u2.trans s2) hα.le
  nlinarith

lemma persp_mul (G : ℝ → ℝ) (p t : ℝ) : persp G p (p * t) = p * G t := by
  unfold persp
  rcases eq_or_ne p 0 with h | h
  · subst h; simp
  · rw [mul_div_cancel_left₀ _ h]

variable {m k : ℕ}

/-- `E| |g||g′| − p̄ | ≤ (2√5/√m)·p̄` for a ReLU layer, `p̄ = (m/2)·v·|h||h′|`. -/
theorem relu_layer_pair_abs {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m) (h h' : Fin k → ℝ) :
    ∫ M : Matrix (Fin m) (Fin k) ℝ, |nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) -
        (m : ℝ) / 2 * v * (nrm h * nrm h')| ∂gaussMat m k v ≤
      2 * √5 / √(m : ℝ) * ((m : ℝ) / 2 * v * (nrm h * nrm h')) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 ≤ (m : ℝ) / 2 * v := by positivity
  have hpb0 : 0 ≤ (m : ℝ) / 2 * v * (nrm h * nrm h') := mul_nonneg hs (nrm_mul_nonneg h h')
  rcases eq_or_lt_of_le hpb0 with h0 | h0
  · -- degenerate
    obtain ⟨-, -, -, iP2, uP2⟩ := relu_layer_pair (m := m) hv hm h h'
    have mP : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
        nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) -
          (m : ℝ) / 2 * v * (nrm h * nrm h')) :=
      (((continuous_nrm.measurable.comp (measurable_reluV.comp (measurable_mulVec_right h))).mul
        (continuous_nrm.measurable.comp (measurable_reluV.comp (measurable_mulVec_right h')))).sub
        measurable_const)
    obtain ⟨-, uPa⟩ := integral_abs_le_sqrt (μ := gaussMat m k v) mP iP2
    rw [← h0] at uP2 uPa ⊢
    have h1 : ∫ M : Matrix (Fin m) (Fin k) ℝ,
        (nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) - 0) ^ 2 ∂gaussMat m k v ≤ 0 := by
      simpa using uP2
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_zero] at h2
    simpa using uPa.trans h2
  · have hs' : 0 < (m : ℝ) / 2 * v := by
      rcases eq_or_lt_of_le hs with e | e
      · rw [← e, zero_mul] at h0; exact absurd h0 (lt_irrefl _)
      · exact e
    have hnn : 0 < nrm h * nrm h' := by
      rcases eq_or_lt_of_le (nrm_mul_nonneg h h') with e | e
      · rw [← e, mul_zero] at h0; exact absurd h0 (lt_irrefl _)
      · exact e
    have hn1 : 0 < nrm h := by
      rcases eq_or_lt_of_le (nrm_nonneg h) with e | e
      · rw [← e, zero_mul] at hnn; exact absurd hnn (lt_irrefl _)
      · exact e
    have hn2 : 0 < nrm h' := by
      rcases eq_or_lt_of_le (nrm_nonneg h') with e | e
      · rw [← e, mul_zero] at hnn; exact absurd hnn (lt_irrefl _)
      · exact e
    have hmeas : ∀ h : Fin k → ℝ, Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
        normSq (reluV (M.mulVec h))) := fun h =>
      measurable_normSq.comp (measurable_reluV.comp (measurable_mulVec_right h))
    have hsq : ∀ h : Fin k → ℝ, (√((m : ℝ) / 2 * v) * nrm h) ^ 2 =
        (m : ℝ) / 2 * (v * normSq h) := by
      intro h; rw [mul_pow, Real.sq_sqrt hs, nrm_sq]; ring
    have h4 : ∀ h : Fin k → ℝ, ∫ M, normSq (reluV (M.mulVec h)) ^ 2 ∂gaussMat m k v ≤
        (1 + 5 / (m : ℝ)) * (√((m : ℝ) / 2 * v) * nrm h) ^ 4 := by
      intro h
      rw [(layer_relu_four hv h).2, show (√((m : ℝ) / 2 * v) * nrm h) ^ 4 =
        ((√((m : ℝ) / 2 * v) * nrm h) ^ 2) ^ 2 by ring, hsq]
      apply le_of_eq
      field_simp
      ring
    have hsq0 : 0 < √((m : ℝ) / 2 * v) := Real.sqrt_pos.mpr hs'
    have key := norm_pair_abs (μ := gaussMat m k v) (hmeas h) (hmeas h')
      (fun M => normSq_nonneg _) (fun M => normSq_nonneg _) (layer_relu_four hv h).1
      (layer_relu_four hv h').1 (ε := 5 / (m : ℝ)) (mul_pos hsq0 hn1) (mul_pos hsq0 hn2)
      (by positivity) (by rw [(layer_relu_sq hv h).2, hsq]) (by rw [(layer_relu_sq hv h').2, hsq])
      (h4 h) (h4 h')
    have e : √((m : ℝ) / 2 * v) * nrm h * (√((m : ℝ) / 2 * v) * nrm h') =
        (m : ℝ) / 2 * v * (nrm h * nrm h') := by
      have := Real.mul_self_sqrt hs
      calc _ = (√((m : ℝ) / 2 * v) * √((m : ℝ) / 2 * v)) * (nrm h * nrm h') := by ring
        _ = _ := by rw [this]
    rw [e] at key
    refine key.2.trans (le_of_eq ?_)
    rw [Real.sqrt_div (by norm_num)]
    ring

/-- **The upper bound of one ReLU layer.** -/
theorem relu_layer_upper {G : ℝ → ℝ} (hG : KGood G) {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m)
    (h h' : Fin k → ℝ) :
    ∫ M : Matrix (Fin m) (Fin k) ℝ, psi G (reluV (M.mulVec h)) (reluV (M.mulVec h'))
      ∂gaussMat m k v ≤
    (m : ℝ) / 2 * v * (psi (G ∘ kappa) h h' +
      (√6 + 2 * √5 * G 0) / √(m : ℝ) * (nrm h * nrm h')) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  set pb : ℝ := (m : ℝ) / 2 * v * (nrm h * nrm h') with hpb
  have hpb0 : 0 ≤ pb := mul_nonneg (by positivity) (nrm_mul_nonneg h h')
  set t := kappa (cosv h h') with ht
  have ht01 := kappa_mem (cosv_mem h h').1 (cosv_mem h h').2
  have hcb : |pb * t| ≤ pb := by
    rw [abs_of_nonneg (mul_nonneg hpb0 ht01.1)]
    nlinarith
  obtain ⟨hRi, -⟩ := relu_layer_lower (m := m) hG hv hm h h'
  obtain ⟨-, -, -, iP2, uP2⟩ := relu_layer_pair (m := m) hv hm h h'
  obtain ⟨iC2, uC2⟩ := layer_dot_relu_var (m := m) hv h h'
  have ec : (m : ℝ) / 2 * (v * kernelPhi h h') = pb * t := by
    rw [kernelPhi_eq_psi]; unfold psi; rw [hpb, ht]; ring
  rw [ec] at iC2 uC2
  rw [← hpb] at iP2 uP2
  have mP : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) - pb) :=
    (((continuous_nrm.measurable.comp (measurable_reluV.comp (measurable_mulVec_right h))).mul
      (continuous_nrm.measurable.comp (measurable_reluV.comp (measurable_mulVec_right h')))).sub
      measurable_const)
  have mC : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - pb * t) :=
    (measurable_dotp_comp (measurable_reluV.comp (measurable_mulVec_right h))
      (measurable_reluV.comp (measurable_mulVec_right h'))).sub measurable_const
  obtain ⟨iPa, uPa⟩ := integral_abs_le_sqrt (μ := gaussMat m k v) mP iP2
  obtain ⟨iCa, uCa⟩ := integral_abs_le_sqrt (μ := gaussMat m k v) mC iC2
  -- the two square roots
  have s1 : √(25 / (m : ℝ) * pb ^ 2) = 5 / √(m : ℝ) * pb := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hpb0, Real.sqrt_div (by norm_num),
      show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have s2 : √(3 / 2 * (m : ℝ) * v ^ 2 * normSq h * normSq h') = √6 / √(m : ℝ) * pb := by
    have e : 3 / 2 * (m : ℝ) * v ^ 2 * normSq h * normSq h' = 6 / (m : ℝ) * pb ^ 2 := by
      rw [hpb, ← nrm_sq h, ← nrm_sq h']; field_simp; ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hpb0, Real.sqrt_div (by norm_num)]
  have b1 : ∫ M : Matrix (Fin m) (Fin k) ℝ,
      |nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) - pb| ∂gaussMat m k v ≤
      2 * √5 / √(m : ℝ) * pb := relu_layer_pair_abs hv hm h h'
  have b2 : ∫ M : Matrix (Fin m) (Fin k) ℝ,
      |dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - pb * t| ∂gaussMat m k v ≤
      √6 / √(m : ℝ) * pb := by
    rw [← s2]; exact uCa.trans (Real.sqrt_le_sqrt uC2)
  have hbnd : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => pb * G t +
      G 0 * |nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) - pb| +
      |dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - pb * t|) (gaussMat m k v) :=
    ((integrable_const _).add (iPa.const_mul _)).add iCa
  have hmono := integral_mono hRi hbnd (fun M => by
    have := psi_le hG (reluV (M.mulVec h)) (reluV (M.mulVec h')) hpb0 hcb
    rw [persp_mul] at this
    exact this)
  have hbnd1 : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => pb * G t +
      G 0 * |nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) - pb|) (gaussMat m k v) :=
    (integrable_const _).add (iPa.const_mul _)
  have a1 := integral_add hbnd1 iCa
  have a2 := integral_add (integrable_const (pb * G t)) (iPa.const_mul (G 0))
  have a3 : ∫ M : Matrix (Fin m) (Fin k) ℝ,
      G 0 * |nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) - pb| ∂gaussMat m k v =
      G 0 * ∫ M : Matrix (Fin m) (Fin k) ℝ,
      |nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) - pb| ∂gaussMat m k v :=
    integral_const_mul _ _
  beta_reduce at a1 a2
  rw [a1, a2, a3] at hmono
  simp only [integral_const, probReal_univ, one_smul] at hmono
  have b1' := mul_le_mul_of_nonneg_left b1 hG0
  have e : (m : ℝ) / 2 * v * (psi (G ∘ kappa) h h' +
      (√6 + 2 * √5 * G 0) / √(m : ℝ) * (nrm h * nrm h')) =
      pb * G t + G 0 * (2 * √5 / √(m : ℝ) * pb) + √6 / √(m : ℝ) * pb := by
    rw [hpb, ht]; unfold psi; simp only [Function.comp]; ring
  rw [e]
  linarith

variable {m₁ m₂ : ℕ}

/-- The two hidden layers, upper bound. -/
theorem hid2_dot_upper {v₁ v₂ : ℝ} (h₁ : 0 ≤ v₁) (h₂ : 0 ≤ v₂) (hm₁ : 1 ≤ m₁)
    (y y' : Fin k → ℝ) :
    ∫ θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ,
        dotp (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y') ∂((gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂)) ≤
    (m₂ : ℝ) / 2 * v₂ * ((m₁ : ℝ) / 2 * v₁ *
        (psi (kappa ∘ kappa) y y' + (√6 + 2 * √5 * kappa 0) / √(m₁ : ℝ) * (nrm y * nrm y'))) := by
  obtain ⟨hi, -⟩ := relu_layer_lower (m := m₁) kGood_kappa h₁ hm₁ y y'
  have hu := relu_layer_upper (m := m₁) kGood_kappa h₁ hm₁ y y'
  have key := integral_prod_le (hid2_dot_integrable (m₂ := m₂) h₁ h₂ y y')
    (g := fun M₁ => (m₂ : ℝ) / 2 * v₂ * psi kappa (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y')))
    (hi.const_mul _) (fun M₁ => by
      have := (layer_dot_relu (m := m₂) h₂ (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y'))).2
      rw [kernelPhi_eq_psi] at this
      apply le_of_eq
      rw [← mul_assoc] at this
      exact this)
  have a1 : ∫ M₁ : Matrix (Fin m₁) (Fin k) ℝ, (m₂ : ℝ) / 2 * v₂ *
      psi kappa (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y')) ∂gaussMat m₁ k v₁ =
      (m₂ : ℝ) / 2 * v₂ * ∫ M₁ : Matrix (Fin m₁) (Fin k) ℝ,
      psi kappa (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y')) ∂gaussMat m₁ k v₁ :=
    integral_const_mul _ _
  rw [a1] at key
  exact key.trans (mul_le_mul_of_nonneg_left hu (by positivity))

variable {n mF : ℕ}

/-- **The two hidden layers of `F`, upper bound** (paper: onW2c (7) for `F`). -/
theorem KF_upper (hn : 1 ≤ n) (hmF : 1 ≤ mF) (y y' : Fin n → ℝ) :
    ∫ F : MlpParam n mF 1, 2 / (mF : ℝ) * dotp (hid2 F.1 F.2.1 y) (hid2 F.1 F.2.1 y')
        ∂mlpGauss n mF 1 ≤
    2 / (n : ℝ) * (psi (kappa ∘ kappa) y y' +
      (√6 + 2 * √5 * kappa 0) / √(mF : ℝ) * (nrm y * nrm y')) := by
  have hmF' : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hi := hid2_dot_integrable (m₁ := mF) (m₂ := mF) (two_div_nonneg n) (two_div_nonneg mF) y y'
  have hu := hid2_dot_upper (m₁ := mF) (m₂ := mF) (two_div_nonneg n) (two_div_nonneg mF) hmF y y'
  have he : ∫ F : MlpParam n mF 1, dotp (hid2 F.1 F.2.1 y) (hid2 F.1 F.2.1 y') ∂mlpGauss n mF 1 =
      ∫ θ : Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ,
        dotp (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y')
        ∂((gaussMat mF n (2 / (n : ℝ))).prod (gaussMat mF mF (2 / (mF : ℝ)))) := by
    unfold mlpGauss; exact integral_drop3 hi.aestronglyMeasurable
  rw [integral_const_mul, he]
  have h2 := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 2 / (mF : ℝ))
  refine le_trans h2 (le_of_eq ?_)
  field_simp

end BstLean.Part132

open BstLean.Part132 in
#print axioms relu_layer_upper
open BstLean.Part132 in
#print axioms KF_upper
