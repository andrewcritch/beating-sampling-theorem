import BstLean.Part133All

/-!
# Part 135 (tools): upper bounds of the mean of the kernel through a whole network

Mirror of `lin_layer_lower`, `mlp_psi_lower`, `kern_pair_lower` of Part 132.

* `persp_upper_pt`: the pointwise bound `L_G(p, c) ≤ p⁺·G(τ) + δ/2 + |δ|/2`, `δ = c − τ·p⁺`,
  for `p ≤ p⁺` (supporting line of `G` at `c/p`).
* `lin_layer_upper`: `E Ψ_G(Mh, Mh′) ≤ m·v·[Ψ_G(h, h′) + (1/(2√m))·|h||h′|]`.
* `mlp_psi_upper`: `E Ψ_G(N(z), N(z′)) ≤ (2q/k)·[Ψ_{G∘κ∘κ}(z, z′) +
  (1/(2√q) + (√6 + 2√5·G(0))/√m + (√6 + 2√5)/√m)·|z||z′|]`.
* `kern_pair_upper`: for unit `x, x′`, `E kern F A A x x′ ≤ (4/n)·[κ^{∘4}(⟨x, x′⟩) + eAup]`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part135

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133

/-! ## Pointwise tools -/

/-- The pointwise upper bound of the perspective: for `p ≤ p⁺` and a reference cosine `τ`,
`L_G(p, c) ≤ G(τ)·p⁺ + δ/2 + |δ|/2` with `δ = c − τ·p⁺`. -/
lemma persp_upper_pt {G : ℝ → ℝ} (hG : KGood G) {p c pp τ : ℝ} (hp : 0 ≤ p) (hc : |c| ≤ p)
    (hpp : p ≤ pp) (hτ : τ ∈ Icc (-1 : ℝ) 1) :
    persp G p c ≤ G τ * pp + 1 / 2 * (c - τ * pp) + 1 / 2 * |c - τ * pp| := by
  have hGτ := hG.nonneg_on hτ
  have hpp0 : 0 ≤ pp := hp.trans hpp
  rcases eq_or_lt_of_le hp with h | h
  · subst h
    have h1 : persp G 0 c = 0 := by simp [persp]
    rw [h1]
    have h2 := neg_abs_le (c - τ * pp)
    have h3 := mul_nonneg hGτ hpp0
    linarith
  · obtain ⟨a, b, ha0, -, hb0, hb1, heq, hab⟩ := hG.support (div_mem_Icc hp hc)
    have h1 : persp G p c = a * p + b * c := persp_eq heq (by field_simp)
    have h2 := hab τ hτ
    have h3 := mul_le_mul_of_nonneg_right h2 hpp0
    have h4 : a * p ≤ a * pp := mul_le_mul_of_nonneg_left hpp ha0
    have h5 : b * (c - τ * pp) ≤ 1 / 2 * (c - τ * pp) + 1 / 2 * |c - τ * pp| := by
      rcases le_total 0 (c - τ * pp) with hd | hd
      · rw [abs_of_nonneg hd]
        nlinarith [mul_le_mul_of_nonneg_right hb1 hd]
      · rw [abs_of_nonpos hd]
        nlinarith [mul_nonneg hb0 (neg_nonneg.mpr hd)]
    rw [h1]
    nlinarith

lemma nrm_smul_of_nonneg {ι : Type*} [Fintype ι] {s : ℝ} (hs : 0 ≤ s) (y : ι → ℝ) :
    nrm (s • y) = s * nrm y := by
  unfold nrm
  rw [normSq_smul, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

/-- `Ψ_G` is homogeneous of degree 1 in each argument. -/
lemma psi_smul_smul {ι : Type*} [Fintype ι] (G : ℝ → ℝ) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (y y' : ι → ℝ) : psi G (s • y) (s' • y') = s * s' * psi G y y' := by
  unfold psi cosv
  rw [nrm_smul_of_nonneg hs.le, nrm_smul_of_nonneg hs'.le, dotp_smul_smul]
  have e : s * s' * dotp y y' / (s * nrm y * (s' * nrm y')) = dotp y y' / (nrm y * nrm y') := by
    rw [show s * nrm y * (s' * nrm y') = s * s' * (nrm y * nrm y') by ring]
    exact mul_div_mul_left _ _ (mul_pos hs hs').ne'
  rw [e]
  ring

/-! ## One linear layer -/

/-- The linear layer for unit vectors. -/
theorem lin_layer_upper_unit {m k : ℕ} {G : ℝ → ℝ} (hG : KGood G) {v : ℝ} (hv : 0 ≤ v)
    (hm : 1 ≤ m) {h h' : Fin k → ℝ} (hh : normSq h = 1) (hh' : normSq h' = 1) :
    ∫ M : Matrix (Fin m) (Fin k) ℝ, psi G (M.mulVec h) (M.mulVec h') ∂gaussMat m k v ≤
      (m : ℝ) * v * (G (dotp h h') + 1 / (2 * √(m : ℝ))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hτm : dotp h h' ∈ Icc (-1 : ℝ) 1 := by
    have := abs_dotp_le_nrm h h'
    rw [nrm_of_normSq_one hh, nrm_of_normSq_one hh', mul_one] at this
    exact abs_le.mp this
  obtain ⟨hint, -⟩ := lin_layer_lower (m := m) hG hv hm h h'
  obtain ⟨i1, e1⟩ := layer_lin_sq (m := m) hv h
  obtain ⟨i2, e2⟩ := layer_lin_sq (m := m) hv h'
  obtain ⟨ic, ec⟩ := layer_dot_lin (m := m) hv h h'
  obtain ⟨iD2, eD2⟩ := lin_ctp_var (m := m) hv hh hh'
  rw [hh, mul_one] at e1
  rw [hh', mul_one] at e2
  have iP : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (M.mulVec h) + normSq (M.mulVec h')) / 2) (gaussMat m k v) :=
    (i1.add i2).div_const 2
  have eP : ∫ M : Matrix (Fin m) (Fin k) ℝ, (normSq (M.mulVec h) + normSq (M.mulVec h')) / 2
      ∂gaussMat m k v = (m : ℝ) * v := by
    rw [integral_div, integral_add i1 i2, e1, e2]; ring
  have iτP : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) (gaussMat m k v) :=
    iP.const_mul _
  have iD : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => dotp (M.mulVec h) (M.mulVec h') -
      dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) (gaussMat m k v) :=
    ic.sub iτP
  have eD : ∫ M : Matrix (Fin m) (Fin k) ℝ, (dotp (M.mulVec h) (M.mulVec h') -
      dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) ∂gaussMat m k v = 0 := by
    have a := integral_sub ic iτP
    beta_reduce at a
    rw [a, integral_const_mul, ec, eP]; ring
  have mD : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => dotp (M.mulVec h) (M.mulVec h') -
      dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) :=
    (measurable_dotp_comp (measurable_mulVec_right h) (measurable_mulVec_right h')).sub
      ((((measurable_normSq.comp (measurable_mulVec_right h)).add
        (measurable_normSq.comp (measurable_mulVec_right h'))).div_const 2).const_mul _)
  obtain ⟨iA, uA⟩ := integral_abs_le_sqrt (μ := gaussMat m k v) mD iD2
  have uA' := uA.trans (le_of_eq (congrArg Real.sqrt eD2))
  have hx0 : 0 ≤ 1 - dotp h h' ^ 2 := by nlinarith [hτm.1, hτm.2]
  have hx2 : 1 - dotp h h' ^ 2 ≤ 1 := by nlinarith [sq_nonneg (dotp h h')]
  have hx1 : (1 - dotp h h' ^ 2) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx2)]
  have hsq : √((m : ℝ) * v ^ 2 * (1 - dotp h h' ^ 2) ^ 2) ≤ √(m : ℝ) * v := by
    have h1 : (m : ℝ) * v ^ 2 * (1 - dotp h h' ^ 2) ^ 2 ≤ (√(m : ℝ) * v) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hm'.le]
      exact mul_le_of_le_one_right (by positivity) hx1
    calc √((m : ℝ) * v ^ 2 * (1 - dotp h h' ^ 2) ^ 2) ≤ √((√(m : ℝ) * v) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = √(m : ℝ) * v := Real.sqrt_sq (by positivity)
  have hI := uA'.trans hsq
  -- the bound function
  have iT1 : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      G (dotp h h') * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) (gaussMat m k v) :=
    iP.const_mul _
  have iT2 : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      1 / 2 * (dotp (M.mulVec h) (M.mulVec h') -
        dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2))) (gaussMat m k v) :=
    iD.const_mul _
  have iT3 : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      1 / 2 * |dotp (M.mulVec h) (M.mulVec h') -
        dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)|) (gaussMat m k v) :=
    iA.const_mul _
  have iT12 : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      G (dotp h h') * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2) +
      1 / 2 * (dotp (M.mulVec h) (M.mulVec h') -
        dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2))) (gaussMat m k v) :=
    iT1.add iT2
  have hB : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      G (dotp h h') * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2) +
      1 / 2 * (dotp (M.mulVec h) (M.mulVec h') -
        dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) +
      1 / 2 * |dotp (M.mulVec h) (M.mulVec h') -
        dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)|) (gaussMat m k v) :=
    iT12.add iT3
  have hmono := integral_mono hint hB (fun M => by
    rw [psi_eq_persp]
    exact persp_upper_pt hG (nrm_mul_nonneg _ _) (abs_dotp_le_nrm (M.mulVec h) (M.mulVec h'))
      (nrm_mul_le _ _) hτm)
  have a1 := integral_add iT12 iT3
  have a2 := integral_add iT1 iT2
  have a3 : ∫ M : Matrix (Fin m) (Fin k) ℝ,
      G (dotp h h') * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2) ∂gaussMat m k v =
      G (dotp h h') * ∫ M : Matrix (Fin m) (Fin k) ℝ,
        (normSq (M.mulVec h) + normSq (M.mulVec h')) / 2 ∂gaussMat m k v :=
    integral_const_mul _ _
  have a4 : ∫ M : Matrix (Fin m) (Fin k) ℝ, 1 / 2 * (dotp (M.mulVec h) (M.mulVec h') -
        dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) ∂gaussMat m k v =
      1 / 2 * ∫ M : Matrix (Fin m) (Fin k) ℝ, (dotp (M.mulVec h) (M.mulVec h') -
        dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) ∂gaussMat m k v :=
    integral_const_mul _ _
  have a5 : ∫ M : Matrix (Fin m) (Fin k) ℝ, 1 / 2 * |dotp (M.mulVec h) (M.mulVec h') -
        dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)| ∂gaussMat m k v =
      1 / 2 * ∫ M : Matrix (Fin m) (Fin k) ℝ, |dotp (M.mulVec h) (M.mulVec h') -
        dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)| ∂gaussMat m k v :=
    integral_const_mul _ _
  beta_reduce at a1 a2
  rw [a1, a2, a3, a4, a5, eP, eD] at hmono
  have hs : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hm'.le
  have hne : √(m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hm').ne'
  have es : (m : ℝ) * v * (1 / (2 * √(m : ℝ))) = 1 / 2 * (√(m : ℝ) * v) := by
    calc (m : ℝ) * v * (1 / (2 * √(m : ℝ)))
        = (√(m : ℝ) * √(m : ℝ)) * v * (1 / (2 * √(m : ℝ))) := by rw [hs]
      _ = 1 / 2 * (√(m : ℝ) * v) * (√(m : ℝ) / √(m : ℝ)) := by ring
      _ = 1 / 2 * (√(m : ℝ) * v) := by rw [div_self hne, mul_one]
  rw [mul_add, es]
  linarith

/-- One linear layer, UPPER bound of the mean. -/
theorem lin_layer_upper {m k : ℕ} {G : ℝ → ℝ} (hG : KGood G) {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m)
    (h h' : Fin k → ℝ) :
    ∫ M : Matrix (Fin m) (Fin k) ℝ, psi G (M.mulVec h) (M.mulVec h') ∂gaussMat m k v ≤
      (m : ℝ) * v * (psi G h h' + 1 / (2 * √(m : ℝ)) * (nrm h * nrm h')) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hrhs : 0 ≤ (m : ℝ) * v * (psi G h h' + 1 / (2 * √(m : ℝ)) * (nrm h * nrm h')) :=
    mul_nonneg (mul_nonneg hm'.le hv) (add_nonneg (psi_nonneg hG h h')
      (mul_nonneg (by positivity) (nrm_mul_nonneg h h')))
  by_cases hz : normSq h = 0
  · have hae := lin_normSq_ae_zero (m := m) hv h (by rw [hz, mul_zero])
    have hz0 : (fun M : Matrix (Fin m) (Fin k) ℝ => psi G (M.mulVec h) (M.mulVec h'))
        =ᵐ[gaussMat m k v] fun _ => (0 : ℝ) := hae.mono fun M hM => psi_zero_left G hM _
    rw [integral_congr_ae hz0, integral_zero]
    exact hrhs
  by_cases hz' : normSq h' = 0
  · have hae := lin_normSq_ae_zero (m := m) hv h' (by rw [hz', mul_zero])
    have hz0 : (fun M : Matrix (Fin m) (Fin k) ℝ => psi G (M.mulVec h) (M.mulVec h'))
        =ᵐ[gaussMat m k v] fun _ => (0 : ℝ) := hae.mono fun M hM => psi_zero_right G _ hM
    rw [integral_congr_ae hz0, integral_zero]
    exact hrhs
  have hσ : 0 < nrm h := nrm_pos_of_ne hz
  have hσ' : 0 < nrm h' := nrm_pos_of_ne hz'
  have hunit : ∀ u : Fin k → ℝ, 0 < nrm u → normSq ((nrm u)⁻¹ • u) = 1 := by
    intro u hu
    rw [normSq_smul, ← nrm_sq u, ← mul_pow, inv_mul_cancel₀ hu.ne', one_pow]
  have hmv : ∀ (M : Matrix (Fin m) (Fin k) ℝ) (u : Fin k → ℝ), 0 < nrm u →
      M.mulVec u = nrm u • M.mulVec ((nrm u)⁻¹ • u) := by
    intro M u hu
    rw [Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hu.ne', one_smul]
  have key := lin_layer_upper_unit (m := m) hG hv hm (hunit h hσ) (hunit h' hσ')
  have eM : (fun M : Matrix (Fin m) (Fin k) ℝ => psi G (M.mulVec h) (M.mulVec h')) =
      fun M : Matrix (Fin m) (Fin k) ℝ => nrm h * nrm h' *
        psi G (M.mulVec ((nrm h)⁻¹ • h)) (M.mulVec ((nrm h')⁻¹ • h')) := by
    funext M
    rw [← psi_smul_smul G hσ hσ', ← hmv M h hσ, ← hmv M h' hσ']
  have ed : dotp ((nrm h)⁻¹ • h) ((nrm h')⁻¹ • h') = cosv h h' := by
    rw [dotp_smul_smul]
    unfold cosv
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [ed] at key
  rw [eM, integral_const_mul]
  calc nrm h * nrm h' * ∫ M : Matrix (Fin m) (Fin k) ℝ,
        psi G (M.mulVec ((nrm h)⁻¹ • h)) (M.mulVec ((nrm h')⁻¹ • h')) ∂gaussMat m k v
      ≤ nrm h * nrm h' * ((m : ℝ) * v * (G (cosv h h') + 1 / (2 * √(m : ℝ)))) :=
        mul_le_mul_of_nonneg_left key (nrm_mul_nonneg h h')
    _ = (m : ℝ) * v * (psi G h h' + 1 / (2 * √(m : ℝ)) * (nrm h * nrm h')) := by
        unfold psi; ring

/-! ## A whole network -/

lemma up_arith {c s S Ψ p0 I1 I2 E E' E'' : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c * s = S)
    (hRu : I1 ≤ s * (Ψ + E' * p0)) (h5 : E * I2 ≤ E * (s * p0)) (e4 : E' * p0 ≤ E'' * p0) :
    c * (I1 + E * I2) ≤ S * (Ψ + (E + E'') * p0) := by
  subst hcs
  have h6 := mul_le_mul_of_nonneg_left e4 hs
  have h7 : I1 + E * I2 ≤ s * (Ψ + (E + E'') * p0) := by nlinarith
  calc c * (I1 + E * I2) ≤ c * (s * (Ψ + (E + E'') * p0)) := mul_le_mul_of_nonneg_left h7 hc
    _ = c * s * (Ψ + (E + E'') * p0) := by ring

/-- The last two matrices, for fixed first hidden vectors `g, g′`: upper bound. -/
theorem tail_psi_upper {m₁ m₂ q : ℕ} {G : ℝ → ℝ} (hG : KGood G) {v₂ v₃ : ℝ} (h₂ : 0 ≤ v₂)
    (h₃ : 0 ≤ v₃) (hm₂ : 1 ≤ m₂) (hq : 1 ≤ q) (g g' : Fin m₁ → ℝ) :
    ∫ θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ,
        psi G (θ.2.mulVec (reluV (θ.1.mulVec g))) (θ.2.mulVec (reluV (θ.1.mulVec g')))
        ∂((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) ≤
      (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂) *
        (psi (G ∘ kappa) g g' +
          ((√6 + 2 * √5 * G 0) / √(m₂ : ℝ) + 1 / (2 * √(q : ℝ))) * (nrm g * nrm g')) := by
  have hm' : (0 : ℝ) < m₂ := by exact_mod_cast hm₂
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨hint, -⟩ := tail_psi_lower (m₁ := m₁) (m₂ := m₂) (q := q) hG h₂ h₃ hm₂ hq g g'
  obtain ⟨hRi, -⟩ := relu_layer_lower (m := m₂) hG h₂ hm₂ g g'
  have hRu := relu_layer_upper (m := m₂) hG h₂ hm₂ g g'
  obtain ⟨hPi, hPu, -, -, -⟩ := relu_layer_pair (m := m₂) h₂ hm₂ g g'
  have hgi : Integrable (fun M₂ : Matrix (Fin m₂) (Fin m₁) ℝ => (q : ℝ) * v₃ *
      (psi G (reluV (M₂.mulVec g)) (reluV (M₂.mulVec g')) + 1 / (2 * √(q : ℝ)) *
        (nrm (reluV (M₂.mulVec g)) * nrm (reluV (M₂.mulVec g'))))) (gaussMat m₂ m₁ v₂) :=
    (hRi.add (hPi.const_mul _)).const_mul _
  have key := integral_prod_le hint hgi (fun M₂ =>
    lin_layer_upper (m := q) hG h₃ hq (reluV (M₂.mulVec g)) (reluV (M₂.mulVec g')))
  refine key.trans ?_
  have a1 : ∫ M₂ : Matrix (Fin m₂) (Fin m₁) ℝ, (q : ℝ) * v₃ *
      (psi G (reluV (M₂.mulVec g)) (reluV (M₂.mulVec g')) + 1 / (2 * √(q : ℝ)) *
        (nrm (reluV (M₂.mulVec g)) * nrm (reluV (M₂.mulVec g')))) ∂gaussMat m₂ m₁ v₂ =
      (q : ℝ) * v₃ * ∫ M₂ : Matrix (Fin m₂) (Fin m₁) ℝ,
      (psi G (reluV (M₂.mulVec g)) (reluV (M₂.mulVec g')) + 1 / (2 * √(q : ℝ)) *
        (nrm (reluV (M₂.mulVec g)) * nrm (reluV (M₂.mulVec g')))) ∂gaussMat m₂ m₁ v₂ :=
    integral_const_mul _ _
  have a2 := integral_add hRi (hPi.const_mul (1 / (2 * √(q : ℝ))))
  have a3 : ∫ M₂ : Matrix (Fin m₂) (Fin m₁) ℝ, 1 / (2 * √(q : ℝ)) *
      (nrm (reluV (M₂.mulVec g)) * nrm (reluV (M₂.mulVec g'))) ∂gaussMat m₂ m₁ v₂ =
      1 / (2 * √(q : ℝ)) * ∫ M₂ : Matrix (Fin m₂) (Fin m₁) ℝ,
      nrm (reluV (M₂.mulVec g)) * nrm (reluV (M₂.mulVec g')) ∂gaussMat m₂ m₁ v₂ :=
    integral_const_mul _ _
  beta_reduce at a2
  rw [a1, a2, a3]
  have hc : (0 : ℝ) ≤ 1 / (2 * √(q : ℝ)) := by positivity
  have h5 := mul_le_mul_of_nonneg_left hPu hc
  have hfin := up_arith (c := (q : ℝ) * v₃) (s := (m₂ : ℝ) / 2 * v₂) (by positivity)
    (by positivity) rfl hRu h5 (le_refl _)
  refine hfin.trans (le_of_eq ?_)
  ring

/-- The whole network, UPPER bound of the mean (mirror of `mlp_psi_lower`). -/
theorem mlp_psi_upper {k q : ℕ} {G : ℝ → ℝ} (hG : KGood G) {m : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q)
    (z z' : Fin k → ℝ) :
    ∫ θ : MlpParam k m q, psi G (mlpEval θ z) (mlpEval θ z') ∂mlpGauss k m q ≤
      2 * (q : ℝ) / k * (psi (G ∘ kappa ∘ kappa) z z' +
        (1 / (2 * √(q : ℝ)) + (√6 + 2 * √5 * G 0) / √(m : ℝ) + (√6 + 2 * √5) / √(m : ℝ)) *
          (nrm z * nrm z')) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have hGk := hG.comp_kappa
  have hGk1 : (G ∘ kappa) 0 ≤ 1 := hGk.le_one KGood.zero_mem
  obtain ⟨hint, -⟩ := mlp_psi_lower (k := k) (q := q) hG hm hq z z'
  have h1 : (0 : ℝ) ≤ 2 / (k : ℝ) := two_div_nonneg k
  have h2 : (0 : ℝ) ≤ 2 / (m : ℝ) := two_div_nonneg m
  obtain ⟨hRi, -⟩ := relu_layer_lower (m := m) hGk h1 hm z z'
  have hRu := relu_layer_upper (m := m) hGk h1 hm z z'
  obtain ⟨hPi, hPu, -, -, -⟩ := relu_layer_pair (m := m) h1 hm z z'
  set c : ℝ := (q : ℝ) * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (m : ℝ))) with hc
  have hc0 : 0 ≤ c := by positivity
  set E : ℝ := (√6 + 2 * √5 * G 0) / √(m : ℝ) + 1 / (2 * √(q : ℝ)) with hE
  have hE0 : 0 ≤ E :=
    add_nonneg (div_nonneg (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) hG0))
      (Real.sqrt_nonneg _)) (by positivity)
  have hgi : Integrable (fun M₁ : Matrix (Fin m) (Fin k) ℝ => c *
      (psi (G ∘ kappa) (reluV (M₁.mulVec z)) (reluV (M₁.mulVec z')) +
        E * (nrm (reluV (M₁.mulVec z)) * nrm (reluV (M₁.mulVec z')))))
      (gaussMat m k (2 / (k : ℝ))) :=
    (hRi.add (hPi.const_mul _)).const_mul _
  unfold mlpGauss at hint ⊢
  have key := integral_prod_le hint hgi (fun M₁ =>
    tail_psi_upper (m₂ := m) (q := q) hG h2 h2 hm hq (reluV (M₁.mulVec z))
      (reluV (M₁.mulVec z')))
  refine key.trans ?_
  have a1 : ∫ M₁ : Matrix (Fin m) (Fin k) ℝ, c *
      (psi (G ∘ kappa) (reluV (M₁.mulVec z)) (reluV (M₁.mulVec z')) +
        E * (nrm (reluV (M₁.mulVec z)) * nrm (reluV (M₁.mulVec z'))))
      ∂gaussMat m k (2 / (k : ℝ)) =
      c * ∫ M₁ : Matrix (Fin m) (Fin k) ℝ,
      (psi (G ∘ kappa) (reluV (M₁.mulVec z)) (reluV (M₁.mulVec z')) +
        E * (nrm (reluV (M₁.mulVec z)) * nrm (reluV (M₁.mulVec z'))))
      ∂gaussMat m k (2 / (k : ℝ)) :=
    integral_const_mul _ _
  have a2 := integral_add hRi (hPi.const_mul E)
  have a3 : ∫ M₁ : Matrix (Fin m) (Fin k) ℝ,
      E * (nrm (reluV (M₁.mulVec z)) * nrm (reluV (M₁.mulVec z'))) ∂gaussMat m k (2 / (k : ℝ)) =
      E * ∫ M₁ : Matrix (Fin m) (Fin k) ℝ,
      nrm (reluV (M₁.mulVec z)) * nrm (reluV (M₁.mulVec z')) ∂gaussMat m k (2 / (k : ℝ)) :=
    integral_const_mul _ _
  beta_reduce at a2
  rw [a1, a2, a3]
  have h5 := mul_le_mul_of_nonneg_left hPu hE0
  have hp0 := nrm_mul_nonneg z z'
  have hs : 0 ≤ (m : ℝ) / 2 * (2 / (k : ℝ)) := by positivity
  have hce : c * ((m : ℝ) / 2 * (2 / (k : ℝ))) = 2 * (q : ℝ) / k := by
    rw [hc]; field_simp
  have e2 : (√6 + 2 * √5 * (G ∘ kappa) 0) / √(m : ℝ) ≤ (√6 + 2 * √5) / √(m : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have h25 : (0 : ℝ) ≤ 2 * √5 := by positivity
    nlinarith
  have e4 := mul_le_mul_of_nonneg_right e2 hp0
  have hfin := up_arith hc0 hs hce hRu h5 e4
  have hcomp : psi (G ∘ kappa ∘ kappa) z z' = psi ((G ∘ kappa) ∘ kappa) z z' := rfl
  refine hfin.trans (le_of_eq ?_)
  rw [hcomp, hE]
  ring

/-! ## The kernel through `A` and `F` -/

/-- The error of the upper bound of the kernel mean at a fixed pair of unit inputs. -/
noncomputable def eAup (n mA mF : ℕ) : ℝ :=
  (√6 + 2 * √5 * kappa 0) / √(mF : ℝ) + 1 / (2 * √(n : ℝ)) +
    (√6 + 2 * √5 * kappa (kappa 0)) / √(mA : ℝ) + (√6 + 2 * √5) / √(mA : ℝ)

lemma kern_up_arith {n' I1 I2 Ψ T C : ℝ} (hn : 0 < n') (hC : 0 ≤ C)
    (h1 : I1 ≤ 2 * n' / n' * (Ψ + T * (1 * 1))) (h2 : I2 ≤ 2 * n' / n' * (1 * 1)) :
    2 / n' * (I1 + C * I2) ≤ 4 / n' * (Ψ + (C + T)) := by
  have e : 2 * n' / n' = 2 := by field_simp
  rw [e] at h1 h2
  have h3 := mul_le_mul_of_nonneg_left h2 hC
  have h4 : I1 + C * I2 ≤ 2 * (Ψ + (C + T)) := by linarith
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 / n')
  calc 2 / n' * (I1 + C * I2) ≤ 2 / n' * (2 * (Ψ + (C + T))) := h5
    _ = 4 / n' * (Ψ + (C + T)) := by ring

/-- Mirror of `kern_pair_lower`: for unit `x, x'`, the mean over `(A, A', F)` of the kernel
`kern F A A x x' = (2/mF)·⟨H_A(x), H_A(x')⟩` is at most `(4/n)(κ^{∘4}(⟨x,x'⟩) + eAup)`. -/
theorem kern_pair_upper {n mA mF : ℕ} (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1, kern p.2.2 p.1 p.1 x x'
        ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) ≤
      4 / (n : ℝ) * (kappa^[4] (dotp x x') + eAup n mA mF) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  obtain ⟨hPi, -⟩ := mlp_psi_lower (k := n) (q := n) hG hmA hn x x'
  have hPu := mlp_psi_upper (k := n) (q := n) hG hmA hn x x'
  obtain ⟨hNi, hNu⟩ := mlp_nrm_upper (k := n) (q := n) hmA x x'
  have hk0 : 0 ≤ kappa 0 := (kappa_mem (by norm_num) (by norm_num)).1
  have hC0 : 0 ≤ (√6 + 2 * √5 * kappa 0) / √(mF : ℝ) :=
    div_nonneg (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) hk0))
      (Real.sqrt_nonneg _)
  have hgi : Integrable (fun a : MlpParam n mA n => 2 / (n : ℝ) *
      (psi (kappa ∘ kappa) (mlpEval a x) (mlpEval a x') +
        (√6 + 2 * √5 * kappa 0) / √(mF : ℝ) *
          (nrm (mlpEval a x) * nrm (mlpEval a x')))) (mlpGauss n mA n) :=
    (hPi.add (hNi.const_mul _)).const_mul _
  have key := integral_prod_le (kern_pair_integrable hn hmA hmF x x') hgi (fun a => by
    have h := KF_upper (mF := mF) hn hmF (mlpEval a x) (mlpEval a x')
    have e : ∫ y : MlpParam n mA n × MlpParam n mF 1, kern y.2 a a x x'
        ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) =
        ∫ F : MlpParam n mF 1, kern F a a x x' ∂mlpGauss n mF 1 := by
      rw [integral_fun_snd (fun F : MlpParam n mF 1 => kern F a a x x')]
      simp
    rw [e]
    exact h)
  refine key.trans ?_
  have a1 : ∫ a : MlpParam n mA n, 2 / (n : ℝ) *
      (psi (kappa ∘ kappa) (mlpEval a x) (mlpEval a x') +
        (√6 + 2 * √5 * kappa 0) / √(mF : ℝ) *
          (nrm (mlpEval a x) * nrm (mlpEval a x'))) ∂mlpGauss n mA n =
      2 / (n : ℝ) * ∫ a : MlpParam n mA n,
      (psi (kappa ∘ kappa) (mlpEval a x) (mlpEval a x') +
        (√6 + 2 * √5 * kappa 0) / √(mF : ℝ) *
          (nrm (mlpEval a x) * nrm (mlpEval a x'))) ∂mlpGauss n mA n :=
    integral_const_mul _ _
  have a2 := integral_add hPi (hNi.const_mul ((√6 + 2 * √5 * kappa 0) / √(mF : ℝ)))
  have a3 : ∫ a : MlpParam n mA n, (√6 + 2 * √5 * kappa 0) / √(mF : ℝ) *
      (nrm (mlpEval a x) * nrm (mlpEval a x')) ∂mlpGauss n mA n =
      (√6 + 2 * √5 * kappa 0) / √(mF : ℝ) * ∫ a : MlpParam n mA n,
      nrm (mlpEval a x) * nrm (mlpEval a x') ∂mlpGauss n mA n := integral_const_mul _ _
  beta_reduce at a2
  rw [a1, a2, a3]
  rw [nrm_of_normSq_one hx, nrm_of_normSq_one hx'] at hPu hNu
  have hpsi : psi ((kappa ∘ kappa) ∘ kappa ∘ kappa) x x' = kappa^[4] (dotp x x') :=
    psi_unit _ hx hx'
  have hq : (kappa ∘ kappa) 0 = kappa (kappa 0) := rfl
  rw [hpsi, hq] at hPu
  have hfin := kern_up_arith hn' hC0 hPu hNu
  refine hfin.trans (le_of_eq ?_)
  unfold eAup
  ring

end BstLean.Part135

open BstLean.Part135 in
#print axioms lin_layer_upper
open BstLean.Part135 in
#print axioms mlp_psi_upper
open BstLean.Part135 in
#print axioms kern_pair_upper
