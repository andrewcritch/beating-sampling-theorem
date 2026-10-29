import BstLean.Part133Four

/-!
# Part 133: the refined `L²` step of one linear layer, and the mean of a norm

Role: `delegations/statements/p133-spec.md`, item 3. Paper source: `onW4c-cx.md` §2 (T2(3)(iii))
and §4 (link `A_3`).

* `persp_le3`: `|L_G(p, c) − L_G(p̄, c̄)| ≤ |c − c̄| + G(0)·|(p − c) − (p̄ − c̄)|` (T2(3)(iii)).
* `lin_layer_L2r`: for one Gaussian matrix `M` with `m` rows,
  `‖Ψ_G(Mh, Mh′) − m·v·Ψ_G(h, h′)‖₂ ≤ [(√(1+τ²) + √2·G(0)(1−τ))/√m + 2·K₄·G(0)/m]·m·v·|h||h′|`.
* `lin_layer_L2s`: the same with `1 + √2·G(0)` (for `τ ≥ 0`, `G(0) ≥ 3/10`).
* `lin_nrm_mean_lower`: `E|Mh| ≥ √(m v)·|h|·(1 − dChi m)`.
* `mlp_nrm_mean_lower`: `E|N(z)| ≥ √(2q/k)·|z|·(1 − dChi q)(1 − epsW m/2)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part133

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131 BstLean.Part132

variable {m k : ℕ}

/-- `K₄(m) = √(12 + 48/m)`: `‖(χ²_m/m − 1)²‖₂ = K₄(m)/m`. -/
noncomputable def K4 (m : ℕ) : ℝ := √(12 + 48 / (m : ℝ))

lemma K4_nonneg (m : ℕ) : 0 ≤ K4 m := Real.sqrt_nonneg _

lemma K4_sq (m : ℕ) : K4 m ^ 2 = 12 + 48 / (m : ℝ) := Real.sq_sqrt (by positivity)

/-! ## `L²` tools -/

section Kit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ} {a b : ℝ}

/-- The triangle inequality with bounds that may be zero. -/
theorem L2le.addR (hf : L2le μ f a) (hg : L2le μ g b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    L2le μ (fun ω => f ω + g ω) (a + b) := by
  have h1 := (hf.mono ha (by linarith : a ≤ a + 1)).add (hg.mono hb (by linarith : b ≤ b + 1))
    (by linarith) (by linarith)
  refine ⟨h1.1, h1.2.1, ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < 4 * (a + b) + 4 := by linarith
  set δ := min 1 (ε / (4 * (a + b) + 4)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε / (4 * (a + b) + 4) := min_le_right _ _
  have h2 := ((hf.mono ha (by linarith : a ≤ a + δ)).add (hg.mono hb (by linarith : b ≤ b + δ))
    (by linarith) (by linarith)).le
  have h3 : δ * (4 * (a + b) + 4) ≤ ε := by rwa [le_div_iff₀ hden] at hδ2
  have h4 : δ * δ ≤ δ := by nlinarith
  nlinarith

lemma L2le.abs (h : L2le μ f a) : L2le μ (fun ω => |f ω|) a :=
  L2le.of_abs_le (continuous_abs.comp_aestronglyMeasurable h.1) h (fun ω => by simp)

lemma L2le_zero_of_ae (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ ω ∂μ, f ω = 0) : L2le μ f 0 := by
  have h2 : (fun ω => f ω ^ 2) =ᵐ[μ] fun _ => (0 : ℝ) := h.mono fun ω hω => by simp [hω]
  refine ⟨hf, (integrable_zero _ _ _).congr h2.symm, ?_⟩
  rw [integral_congr_ae h2]
  simp

end Kit

/-! ## T2(3)(iii) -/

lemma persp_le3_aux {G : ℝ → ℝ} (hG : KGood G) {p c p' c' : ℝ} (hp : 0 ≤ p) (hc : |c| ≤ p)
    (hp' : 0 ≤ p') (hc' : |c'| ≤ p') :
    persp G p c - persp G p' c' ≤ |c - c'| + G 0 * |(p - c) - (p' - c')| := by
  obtain ⟨a, b, ha0, ha1, hb0, hb1, heq, hab⟩ := hG.support (div_mem_Icc hp hc)
  have h1 : persp G p c = a * p + b * c := by
    rcases eq_or_lt_of_le hp with h | h
    · subst h
      have : c = 0 := abs_nonpos_iff.mp hc
      simp [persp, this]
    · exact persp_eq heq (by field_simp)
  have h2 := persp_ge hab hp' hc'
  have hab1 : a + b ≤ 1 := by
    have := hab 1 ⟨by norm_num, le_refl _⟩
    rw [hG.one] at this
    linarith
  have h3 : (a + b) * (c - c') ≤ |c - c'| := by
    calc (a + b) * (c - c') ≤ (a + b) * |c - c'| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
      _ ≤ 1 * |c - c'| := mul_le_mul_of_nonneg_right hab1 (abs_nonneg _)
      _ = |c - c'| := one_mul _
  have h4 : a * ((p - c) - (p' - c')) ≤ G 0 * |(p - c) - (p' - c')| := by
    calc a * ((p - c) - (p' - c')) ≤ a * |(p - c) - (p' - c')| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) ha0
      _ ≤ G 0 * |(p - c) - (p' - c')| := mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
  nlinarith

/-- T2(3)(iii) of the paper. -/
lemma persp_le3 {G : ℝ → ℝ} (hG : KGood G) {p c p' c' : ℝ} (hp : 0 ≤ p) (hc : |c| ≤ p)
    (hp' : 0 ≤ p') (hc' : |c'| ≤ p') :
    |persp G p c - persp G p' c'| ≤ |c - c'| + G 0 * |(p - c) - (p' - c')| := by
  rw [abs_le]
  have h1 := persp_le3_aux hG hp hc hp' hc'
  have h2 := persp_le3_aux hG hp' hc' hp hc
  have e1 : |c' - c| = |c - c'| := abs_sub_comm _ _
  have e2 : |(p' - c') - (p - c)| = |(p - c) - (p' - c')| := abs_sub_comm _ _
  rw [e1, e2] at h2
  constructor <;> linarith

lemma persp_scale (G : ℝ → ℝ) {s : ℝ} (hs : 0 < s) (p c : ℝ) :
    persp G (s * p) (s * c) = s * persp G p c := by
  unfold persp
  rw [mul_div_mul_left _ _ hs.ne']
  ring

/-! ## Pointwise tools -/

lemma half_sq_sub_leR {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s) :
    (a - b) ^ 2 / 2 ≤ ((a ^ 2 - s) ^ 2 + (b ^ 2 - s) ^ 2) / s := by
  obtain ⟨r, hr, hrs⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = s :=
    ⟨√s, Real.sqrt_pos.mpr hs, Real.sq_sqrt hs.le⟩
  have h1 : (a - r) ^ 2 * s ≤ (a ^ 2 - s) ^ 2 := by
    rw [← hrs]
    have e : (a ^ 2 - r ^ 2) ^ 2 = (a - r) ^ 2 * (a + r) ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
  have h2 : (b - r) ^ 2 * s ≤ (b ^ 2 - s) ^ 2 := by
    rw [← hrs]
    have e : (b ^ 2 - r ^ 2) ^ 2 = (b - r) ^ 2 * (b + r) ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
  have h3 : (a - b) ^ 2 / 2 ≤ (a - r) ^ 2 + (b - r) ^ 2 := by
    nlinarith [sq_nonneg (a + b - 2 * r)]
  have h4 := mul_le_mul_of_nonneg_right h3 hs.le
  rw [le_div_iff₀ hs]
  linarith

lemma defect_bound {σ σ' A B s : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ') (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : 0 < s) :
    0 ≤ (σ' / σ * A ^ 2 + σ / σ' * B ^ 2) / 2 - A * B ∧
    (σ' / σ * A ^ 2 + σ / σ' * B ^ 2) / 2 - A * B ≤
      σ * σ' / s * ((A ^ 2 / σ ^ 2 - s) ^ 2 + (B ^ 2 / σ' ^ 2 - s) ^ 2) := by
  have e : (σ' / σ * A ^ 2 + σ / σ' * B ^ 2) / 2 - A * B =
      σ * σ' * ((A / σ - B / σ') ^ 2 / 2) := by
    field_simp
    ring
  rw [e]
  refine ⟨by positivity, ?_⟩
  have h := half_sq_sub_leR (a := A / σ) (b := B / σ') (by positivity) (by positivity) hs
  rw [div_pow, div_pow] at h
  calc σ * σ' * ((A / σ - B / σ') ^ 2 / 2)
      ≤ σ * σ' * (((A ^ 2 / σ ^ 2 - s) ^ 2 + (B ^ 2 / σ' ^ 2 - s) ^ 2) / s) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = σ * σ' / s * ((A ^ 2 / σ ^ 2 - s) ^ 2 + (B ^ 2 / σ' ^ 2 - s) ^ 2) := by ring

lemma key_identity {σ σ' A2 B2 P C s d : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ') :
    (P - C) - (s * (σ * σ') - s * d) =
      1 / (2 * (σ * σ')) * ((σ' ^ 2 * A2 + σ ^ 2 * B2 - 2 * (σ' * σ * C)) -
        s * (σ' ^ 2 * σ ^ 2 + σ ^ 2 * σ' ^ 2 - 2 * (σ' * σ * d))) -
      ((σ' / σ * A2 + σ / σ' * B2) / 2 - P) := by
  field_simp
  ring

lemma nrm_zero_of {ι : Type*} [Fintype ι] {y : ι → ℝ} (h : normSq y = 0) : nrm y = 0 := by
  unfold nrm; rw [h, Real.sqrt_zero]

lemma psi_zero_left {ι : Type*} [Fintype ι] (G : ℝ → ℝ) {y : ι → ℝ} (h : normSq y = 0)
    (y' : ι → ℝ) : psi G y y' = 0 := by
  unfold psi; rw [nrm_zero_of h]; ring

lemma psi_zero_right {ι : Type*} [Fintype ι] (G : ℝ → ℝ) (y : ι → ℝ) {y' : ι → ℝ}
    (h : normSq y' = 0) : psi G y y' = 0 := by
  unfold psi; rw [nrm_zero_of h]; ring

/-- For `v = 0` or `h = 0`: `|M h|² = 0` almost surely. -/
lemma lin_normSq_ae_zero {v : ℝ} (hv : 0 ≤ v) (h : Fin k → ℝ) (hz : v * normSq h = 0) :
    ∀ᵐ M : Matrix (Fin m) (Fin k) ℝ ∂gaussMat m k v, normSq (M.mulVec h) = 0 := by
  obtain ⟨hi, he⟩ := layer_lin_sq (m := m) hv h
  rw [hz, mul_zero] at he
  have := (integral_eq_zero_iff_of_nonneg (fun M => normSq_nonneg _) hi).1 he
  exact this

/-! ## The refined linear layer -/

theorem lin_layer_L2r {G : ℝ → ℝ} (hG : KGood G) {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m)
    (h h' : Fin k → ℝ) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => psi G (M.mulVec h) (M.mulVec h') -
        (m : ℝ) * v * psi G h h')
      (((√(1 + cosv h h' ^ 2) + √2 * G 0 * (1 - cosv h h')) / √(m : ℝ) +
          2 * K4 m * G 0 / (m : ℝ)) * ((m : ℝ) * v * (nrm h * nrm h'))) := by
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      psi G (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * psi G h h') :=
    (measurable_psi_lin hG.cont h h').sub measurable_const
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := K4_nonneg m
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have ht := cosv_mem h h'
  have hbnd : 0 ≤ ((√(1 + cosv h h' ^ 2) + √2 * G 0 * (1 - cosv h h')) / √(m : ℝ) +
      2 * K4 m * G 0 / (m : ℝ)) * ((m : ℝ) * v * (nrm h * nrm h')) := by
    have h1 : 0 ≤ √2 * G 0 * (1 - cosv h h') :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hG0) (by linarith [ht.2])
    have h2 : 0 ≤ nrm h * nrm h' := nrm_mul_nonneg h h'
    have h3 : 0 ≤ √(1 + cosv h h' ^ 2) := Real.sqrt_nonneg _
    have h4 : 0 ≤ √(m : ℝ) := Real.sqrt_nonneg _
    positivity
  -- degenerate cases
  by_cases hz : v * normSq h = 0
  · have hae := lin_normSq_ae_zero (m := m) hv h hz
    have h0 : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
        psi G (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * psi G h h') 0 := by
      refine L2le_zero_of_ae hmeas.aestronglyMeasurable (hae.mono fun M hM => ?_)
      rw [psi_zero_left G hM]
      rcases mul_eq_zero.mp hz with h1 | h1
      · rw [h1]; ring
      · rw [psi_zero_left G h1]; ring
    exact h0.mono le_rfl hbnd
  by_cases hz' : v * normSq h' = 0
  · have hae := lin_normSq_ae_zero (m := m) hv h' hz'
    have h0 : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
        psi G (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * psi G h h') 0 := by
      refine L2le_zero_of_ae hmeas.aestronglyMeasurable (hae.mono fun M hM => ?_)
      rw [psi_zero_right G _ hM]
      rcases mul_eq_zero.mp hz' with h1 | h1
      · rw [h1]; ring
      · rw [psi_zero_right G _ h1]; ring
    exact h0.mono le_rfl hbnd
  -- the main case
  have hv0 : v ≠ 0 := fun hh => hz (by rw [hh, zero_mul])
  have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  have hn0 : normSq h ≠ 0 := fun hh => hz (by rw [hh, mul_zero])
  have hn0' : normSq h' ≠ 0 := fun hh => hz' (by rw [hh, mul_zero])
  have hσ : 0 < nrm h := nrm_pos_of_ne hn0
  have hσ' : 0 < nrm h' := nrm_pos_of_ne hn0'
  have hσ2 : nrm h ^ 2 = normSq h := nrm_sq h
  have hσ2' : nrm h' ^ 2 = normSq h' := nrm_sq h'
  have hdot : dotp h h' = cosv h h' * (nrm h * nrm h') := dotp_eq_cosv_mul h h'
  set σ := nrm h with hσdef
  set σ' := nrm h' with hσdef'
  set τ := cosv h h' with hτdef
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ (m : ℝ) = r ^ 2 :=
    ⟨√(m : ℝ), Real.sqrt_pos.mpr hm', (Real.sq_sqrt hm'.le).symm⟩
  have hsq : √(m : ℝ) = r := by rw [hr]; exact Real.sqrt_sq hr0.le
  have hs : 0 < (m : ℝ) * v := by positivity
  set w : Fin k → ℝ := σ' • h - σ • h' with hwdef
  have hw : normSq w = σ' ^ 2 * σ ^ 2 + σ ^ 2 * σ' ^ 2 - 2 * (σ' * σ * (τ * (σ * σ'))) := by
    rw [hwdef, normSq_sub, normSq_smul, normSq_smul, dotp_smul_smul, hdot, ← hσ2, ← hσ2']
  have hN : ∀ M : Matrix (Fin m) (Fin k) ℝ, normSq (M.mulVec w) =
      σ' ^ 2 * normSq (M.mulVec h) + σ ^ 2 * normSq (M.mulVec h') -
        2 * (σ' * σ * dotp (M.mulVec h) (M.mulVec h')) := by
    intro M
    rw [hwdef, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, normSq_sub,
      normSq_smul, normSq_smul, dotp_smul_smul]
  have mdot : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dotp (M.mulVec h) (M.mulVec h')) :=
    measurable_dotp_comp (measurable_mulVec_right h) (measurable_mulVec_right h')
  have mns : ∀ u : Fin k → ℝ, Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      normSq (M.mulVec u)) := fun u => measurable_normSq.comp (measurable_mulVec_right u)
  have mnr : ∀ u : Fin k → ℝ, Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      nrm (M.mulVec u)) := fun u => continuous_nrm.measurable.comp (measurable_mulVec_right u)
  -- piece 1: the inner product
  have L1 : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dotp (M.mulVec h) (M.mulVec h') - (m : ℝ) * (v * dotp h h'))
      (√(1 + τ ^ 2) / r * ((m : ℝ) * v * (σ * σ'))) := by
    refine ⟨(mdot.sub measurable_const).aestronglyMeasurable, (lin_dot_var0 hv h h').1, ?_⟩
    rw [lin_dot_var hv h h']
    have e : (√(1 + τ ^ 2) / r * ((m : ℝ) * v * (σ * σ'))) ^ 2 =
        (1 + τ ^ 2) / r ^ 2 * ((m : ℝ) * v * (σ * σ')) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by positivity)]
    rw [e, ← hσ2, ← hσ2', hdot, hr]
    apply le_of_eq
    field_simp
  -- piece 2: the squared norm of `M (σ' h − σ h')`
  have L2 : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      1 / (2 * (σ * σ')) * (normSq (M.mulVec w) - (m : ℝ) * (v * normSq w)))
      (√2 * (1 - τ) / r * ((m : ℝ) * v * (σ * σ'))) := by
    obtain ⟨i, e⟩ := lin_sq_var (m := m) hv w
    have h0 : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
        normSq (M.mulVec w) - (m : ℝ) * (v * normSq w)) (√2 * r * (v * normSq w)) := by
      refine ⟨((mns w).sub measurable_const).aestronglyMeasurable, i, ?_⟩
      have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have e3 : (√2 * r * (v * normSq w)) ^ 2 = √2 ^ 2 * r ^ 2 * (v * normSq w) ^ 2 := by ring
      rw [e, e3, h2, hr]
    refine (h0.const_mul_nonneg (c := 1 / (2 * (σ * σ'))) (by positivity)).congr_bound ?_
    rw [hw, hr]
    field_simp
    ring
  -- piece 3: the defect `D`
  have LX : ∀ u : Fin k → ℝ, normSq u ≠ 0 →
      L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
        (nrm (M.mulVec u) ^ 2 / nrm u ^ 2 - (m : ℝ) * v) ^ 2) ((m : ℝ) * K4 m * v ^ 2) := by
    intro u hu
    have hup : 0 < normSq u := lt_of_le_of_ne (normSq_nonneg u) (Ne.symm hu)
    obtain ⟨i4, e4⟩ := lin_sq_four (m := m) hv u
    have ee : ∀ M : Matrix (Fin m) (Fin k) ℝ,
        ((nrm (M.mulVec u) ^ 2 / nrm u ^ 2 - (m : ℝ) * v) ^ 2) ^ 2 =
        1 / normSq u ^ 4 * (normSq (M.mulVec u) - (m : ℝ) * (v * normSq u)) ^ 4 := by
      intro M
      rw [nrm_sq, nrm_sq]
      field_simp
    refine ⟨(((((mnr u).pow_const 2).div_const _).sub measurable_const).pow_const
      2).aestronglyMeasurable, ?_, ?_⟩
    · simp_rw [ee]
      exact i4.const_mul _
    · simp_rw [ee]
      have e3 : ((m : ℝ) * K4 m * v ^ 2) ^ 2 = (m : ℝ) ^ 2 * K4 m ^ 2 * v ^ 4 := by ring
      rw [integral_const_mul, e4, e3, K4_sq]
      apply le_of_eq
      field_simp
  have L3 : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (σ' / σ * normSq (M.mulVec h) + σ / σ' * normSq (M.mulVec h')) / 2 -
        nrm (M.mulVec h) * nrm (M.mulVec h'))
      (2 * K4 m / (m : ℝ) * ((m : ℝ) * v * (σ * σ'))) := by
    have h0 := (((LX h hn0).addR (LX h' hn0') (by positivity) (by positivity)).const_mul_nonneg
      (c := σ * σ' / ((m : ℝ) * v)) (by positivity))
    have h1 : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
        (σ' / σ * normSq (M.mulVec h) + σ / σ' * normSq (M.mulVec h')) / 2 -
          nrm (M.mulVec h) * nrm (M.mulVec h'))
        (σ * σ' / ((m : ℝ) * v) * ((m : ℝ) * K4 m * v ^ 2 + (m : ℝ) * K4 m * v ^ 2)) := by
      refine L2le.of_abs_le ((((((mns h).const_mul _).add ((mns h').const_mul _)).div_const
        2).sub ((mnr h).mul (mnr h'))).aestronglyMeasurable) h0 (fun M => ?_)
      obtain ⟨d1, d2⟩ := defect_bound hσ hσ' (nrm_nonneg (M.mulVec h))
        (nrm_nonneg (M.mulVec h')) hs
      rw [nrm_sq (M.mulVec h), nrm_sq (M.mulVec h')] at d1
      rw [nrm_sq (M.mulVec h), nrm_sq (M.mulVec h')] at d2
      rw [abs_of_nonneg d1]
      refine d2.trans (le_trans (le_of_eq ?_) (le_abs_self _))
      rw [nrm_sq (M.mulVec h), nrm_sq (M.mulVec h')]
    refine h1.congr_bound ?_
    field_simp
    ring
  -- sum
  have a1 : 0 ≤ √(1 + τ ^ 2) / r * ((m : ℝ) * v * (σ * σ')) := by positivity
  have a2 : 0 ≤ √2 * (1 - τ) / r * ((m : ℝ) * v * (σ * σ')) := by
    have : 0 ≤ 1 - τ := by linarith [ht.2]
    positivity
  have a3 : 0 ≤ 2 * K4 m / (m : ℝ) * ((m : ℝ) * v * (σ * σ')) := by positivity
  have L23 := ((L2.abs.addR L3 a2 a3).const_mul_nonneg hG0)
  have Lall := L1.abs.addR L23 a1 (mul_nonneg hG0 (add_nonneg a2 a3))
  rw [hsq]
  refine (L2le.of_abs_le hmeas.aestronglyMeasurable Lall (fun M => ?_)).congr_bound (by ring)
  have hD := (defect_bound hσ hσ' (nrm_nonneg (M.mulVec h)) (nrm_nonneg (M.mulVec h')) hs).1
  rw [nrm_sq (M.mulVec h), nrm_sq (M.mulVec h')] at hD
  have hP := persp_le3 hG (nrm_mul_nonneg (M.mulVec h) (M.mulVec h'))
    (abs_dotp_le_nrm (M.mulVec h) (M.mulVec h'))
    (mul_nonneg hs.le (nrm_mul_nonneg h h'))
    (by rw [abs_mul, abs_of_pos hs]
        exact mul_le_mul_of_nonneg_left (abs_dotp_le_nrm h h') hs.le :
      |(m : ℝ) * v * dotp h h'| ≤ (m : ℝ) * v * (nrm h * nrm h'))
  rw [persp_scale G hs, ← psi_eq_persp, ← psi_eq_persp] at hP
  have hid := key_identity (A2 := normSq (M.mulVec h)) (B2 := normSq (M.mulVec h'))
    (P := nrm (M.mulVec h) * nrm (M.mulVec h')) (C := dotp (M.mulVec h) (M.mulVec h'))
    (s := (m : ℝ) * v) (d := dotp h h') hσ hσ'
  have hw' : normSq w = σ' ^ 2 * σ ^ 2 + σ ^ 2 * σ' ^ 2 - 2 * (σ' * σ * dotp h h') := by
    rw [hw, hdot]
  rw [← hN M, ← hw'] at hid
  have e1 : dotp (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * dotp h h' =
      dotp (M.mulVec h) (M.mulVec h') - (m : ℝ) * (v * dotp h h') := by ring
  have e2 : (m : ℝ) * v * normSq w = (m : ℝ) * (v * normSq w) := by ring
  rw [hid, e1, e2] at hP
  refine hP.trans (le_trans ?_ (le_abs_self _))
  have h5 := abs_sub (1 / (2 * (σ * σ')) * (normSq (M.mulVec w) - (m : ℝ) * (v * normSq w)))
    ((σ' / σ * normSq (M.mulVec h) + σ / σ' * normSq (M.mulVec h')) / 2 -
      nrm (M.mulVec h) * nrm (M.mulVec h'))
  rw [abs_of_nonneg hD] at h5
  have h6 := mul_le_mul_of_nonneg_left h5 hG0
  linarith

theorem lin_layer_L2s {G : ℝ → ℝ} (hG : KGood G) (hG0 : 3 / 10 ≤ G 0) {v : ℝ} (hv : 0 ≤ v)
    (hm : 1 ≤ m) (h h' : Fin k → ℝ) (hd : 0 ≤ dotp h h') :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => psi G (M.mulVec h) (M.mulVec h') -
        (m : ℝ) * v * psi G h h')
      (((1 + √2 * G 0) / √(m : ℝ) + 2 * K4 m * G 0 / (m : ℝ)) *
        ((m : ℝ) * v * (nrm h * nrm h'))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := K4_nonneg m
  have ht := cosv_mem h h'
  have ht0 : 0 ≤ cosv h h' := div_nonneg hd (nrm_mul_nonneg h h')
  have hp : 0 ≤ nrm h * nrm h' := nrm_mul_nonneg h h'
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ √2 := Real.sqrt_nonneg _
  have hs1 : 1 ≤ √2 := by nlinarith
  have hs3 : √2 ≤ 10 / 7 := by nlinarith
  set τ := cosv h h' with hτ
  have h1 : √(1 + τ ^ 2) ≤ 1 + (√2 - 1) * τ := by
    rw [Real.sqrt_le_iff]
    refine ⟨by nlinarith [ht.2], ?_⟩
    have : τ ^ 2 ≤ τ := by nlinarith [ht.2]
    nlinarith [ht.2, mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr this)]
  have h2 : √(1 + τ ^ 2) + √2 * G 0 * (1 - τ) ≤ 1 + √2 * G 0 := by
    have : (√2 - 1 - √2 * G 0) * τ ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ ht0
      nlinarith
    nlinarith
  have h0 : 0 ≤ √(1 + τ ^ 2) + √2 * G 0 * (1 - τ) := by
    have := Real.sqrt_nonneg (1 + τ ^ 2)
    have : 0 ≤ √2 * G 0 * (1 - τ) :=
      mul_nonneg (mul_nonneg hs0 (by linarith)) (by linarith [ht.2])
    linarith
  have hr : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm'
  have hG0' : 0 ≤ G 0 := by linarith
  refine (lin_layer_L2r hG hv hm h h').mono ?_ ?_
  · positivity
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    have := div_le_div_of_nonneg_right h2 hr.le
    linarith

/-! ## The mean of a norm -/

lemma sqrt_ge_cubic {x : ℝ} (hx : 0 ≤ x) :
    1 + (x - 1) / 2 - (x - 1) ^ 2 / 8 - 3 / 8 * |x - 1| ^ 3 ≤ √x := by
  obtain ⟨s, hs0, hsx⟩ : ∃ s : ℝ, 0 ≤ s ∧ √x = s := ⟨√x, Real.sqrt_nonneg x, rfl⟩
  have hxs : x = s ^ 2 := by rw [← hsx, Real.sq_sqrt hx]
  rw [hsx, hxs]
  rcases le_total s 1 with h | h
  · have ha : |s ^ 2 - 1| = 1 - s ^ 2 := by
      rw [abs_of_nonpos (by nlinarith)]; ring
    rw [ha]
    have e : s - (1 + (s ^ 2 - 1) / 2 - (s ^ 2 - 1) ^ 2 / 8 - 3 / 8 * (1 - s ^ 2) ^ 3) =
        (1 - s) ^ 3 * (s * (3 * (1 + s) ^ 2 + 3 * (1 + s) + 2)) / 8 := by ring
    have h1 : 0 ≤ (1 - s) ^ 3 := pow_nonneg (by linarith) 3
    have h2 : 0 ≤ s * (3 * (1 + s) ^ 2 + 3 * (1 + s) + 2) := mul_nonneg hs0 (by nlinarith)
    have := mul_nonneg h1 h2
    linarith
  · have ha : |s ^ 2 - 1| = s ^ 2 - 1 := abs_of_nonneg (by nlinarith)
    rw [ha]
    have e : s - (1 + (s ^ 2 - 1) / 2 - (s ^ 2 - 1) ^ 2 / 8 - 3 / 8 * (s ^ 2 - 1) ^ 3) =
        (s - 1) ^ 2 * ((s + 1) ^ 2 - 4) / 8 + 3 / 8 * (s ^ 2 - 1) ^ 3 := by ring
    have h1 : 0 ≤ (s + 1) ^ 2 - 4 := by nlinarith
    have h2 : 0 ≤ (s ^ 2 - 1) ^ 3 := pow_nonneg (by nlinarith) 3
    have h3 := mul_nonneg (sq_nonneg (s - 1)) h1
    linarith

lemma sqrt_ge_quad' {x : ℝ} (hx : 0 ≤ x) : 1 + (x - 1) / 2 - (x - 1) ^ 2 / 2 ≤ √x := by
  obtain ⟨s, hs0, hsx⟩ : ∃ s : ℝ, 0 ≤ s ∧ √x = s := ⟨√x, Real.sqrt_nonneg x, rfl⟩
  have hxs : x = s ^ 2 := by rw [← hsx, Real.sq_sqrt hx]
  rw [hsx, hxs]
  have e : s - (1 + (s ^ 2 - 1) / 2 - (s ^ 2 - 1) ^ 2 / 2) = (s - 1) ^ 2 * (s ^ 2 + 2 * s) / 2 := by
    ring
  have : 0 ≤ (s - 1) ^ 2 * (s ^ 2 + 2 * s) := mul_nonneg (sq_nonneg _) (by nlinarith)
  linarith

/-- `δ(m) = 1/(4m) + (3√2/8)·K₄(m)/(m√m)`: the relative deficit of `E|Mh|`. -/
noncomputable def dChi (m : ℕ) : ℝ :=
  1 / (4 * (m : ℝ)) + 3 * √2 / 8 * K4 m / ((m : ℝ) * √(m : ℝ))

theorem lin_nrm_mean_lower {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m) (h : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => nrm (M.mulVec h)) (gaussMat m k v) ∧
    √((m : ℝ) * v) * nrm h * (1 - dChi m) ≤
      ∫ M : Matrix (Fin m) (Fin k) ℝ, nrm (M.mulVec h) ∂gaussMat m k v := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have mnr : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => nrm (M.mulVec h)) :=
    continuous_nrm.measurable.comp (measurable_mulVec_right h)
  have mns : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => normSq (M.mulVec h)) :=
    measurable_normSq.comp (measurable_mulVec_right h)
  obtain ⟨i2, e2⟩ := layer_lin_sq (m := m) hv h
  have hi : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => nrm (M.mulVec h)) (gaussMat m k v) := by
    refine integrable_of_sq mnr (fun M => nrm_nonneg _) ?_
    have : (fun M : Matrix (Fin m) (Fin k) ℝ => nrm (M.mulVec h) ^ 2) =
        fun M => normSq (M.mulVec h) := funext fun M => nrm_sq _
    rw [this]
    exact i2
  refine ⟨hi, ?_⟩
  have hint0 : 0 ≤ ∫ M : Matrix (Fin m) (Fin k) ℝ, nrm (M.mulVec h) ∂gaussMat m k v :=
    integral_nonneg fun M => nrm_nonneg _
  by_cases hz : v * normSq h = 0
  · have : √((m : ℝ) * v) * nrm h = 0 := by
      rcases mul_eq_zero.mp hz with h1 | h1
      · rw [h1]; simp
      · rw [nrm_zero_of h1]; ring
    rw [this, zero_mul]
    exact hint0
  have hS : 0 < (m : ℝ) * (v * normSq h) := by
    have := lt_of_le_of_ne (mul_nonneg hv (normSq_nonneg h)) (Ne.symm hz)
    positivity
  have hv0 : v ≠ 0 := fun hh => hz (by rw [hh, zero_mul])
  have hn0 : normSq h ≠ 0 := fun hh => hz (by rw [hh, mul_zero])
  set S := (m : ℝ) * (v * normSq h) with hSdef
  have hc : √((m : ℝ) * v) * nrm h = √S := by
    unfold nrm
    rw [← Real.sqrt_mul (by positivity), hSdef]
    congr 1
    ring
  rw [hc]
  obtain ⟨c, hc0, hcS⟩ : ∃ c : ℝ, 0 ≤ c ∧ √S = c := ⟨√S, Real.sqrt_nonneg _, rfl⟩
  rw [hcS]
  obtain ⟨iv, ev⟩ := lin_sq_var (m := m) hv h
  obtain ⟨i4, e4⟩ := lin_sq_four (m := m) hv h
  let d : Matrix (Fin m) (Fin k) ℝ → ℝ := fun M => 1 / S * (normSq (M.mulVec h) - S)
  have md : Measurable d := (mns.sub measurable_const).const_mul _
  have id1 : Integrable d (gaussMat m k v) := (i2.sub (integrable_const S)).const_mul _
  have ed1 : ∫ M, d M ∂gaussMat m k v = 0 := by
    show ∫ M : Matrix (Fin m) (Fin k) ℝ, 1 / S * (normSq (M.mulVec h) - S) ∂gaussMat m k v = 0
    rw [integral_const_mul, integral_sub i2 (integrable_const S), e2]
    simp
  have hd2 : ∀ M, d M ^ 2 = 1 / S ^ 2 * (normSq (M.mulVec h) - S) ^ 2 := fun M => by
    show (1 / S * (normSq (M.mulVec h) - S)) ^ 2 = _
    rw [mul_pow, one_div, one_div, inv_pow]
  have id2 : Integrable (fun M => d M ^ 2) (gaussMat m k v) := by
    simp_rw [hd2]; exact iv.const_mul _
  have ed2 : ∫ M, d M ^ 2 ∂gaussMat m k v = 2 / (m : ℝ) := by
    simp_rw [hd2]
    rw [integral_const_mul, ev, hSdef]
    field_simp
  have hd4 : ∀ M, (d M ^ 2) ^ 2 = 1 / S ^ 4 * (normSq (M.mulVec h) - S) ^ 4 := fun M => by
    rw [hd2, mul_pow]
    rw [one_div, one_div, inv_pow]
    ring
  have id4 : Integrable (fun M => (d M ^ 2) ^ 2) (gaussMat m k v) := by
    simp_rw [hd4]; exact i4.const_mul _
  have ed4 : ∫ M, (d M ^ 2) ^ 2 ∂gaussMat m k v = (K4 m / (m : ℝ)) ^ 2 := by
    simp_rw [hd4]
    rw [integral_const_mul, e4, div_pow, K4_sq, hSdef]
    field_simp
  obtain ⟨i3, e3⟩ := integral_mul_le_sqrt (μ := gaussMat m k v) md (md.pow_const 2) id2 id4
  rw [ed2, ed4, Real.sqrt_sq (div_nonneg (K4_nonneg m) hm'.le), Real.sqrt_div (by norm_num)] at e3
  obtain ⟨iL, eL⟩ := integral_lin4 (μ := gaussMat m k v) id1 id2 i3 i3 c (c / 2) (c / 8)
    (3 * c / 8) 0
  have hpt : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      c / 2 * d M + c - c / 8 * d M ^ 2 - 3 * c / 8 * (|d M| * |d M ^ 2|) -
        0 * (|d M| * |d M ^ 2|) ≤ nrm (M.mulVec h) := by
    intro M
    have hx : 0 ≤ normSq (M.mulVec h) / S := div_nonneg (normSq_nonneg _) hS.le
    have h1 := sqrt_ge_cubic hx
    have hdx : normSq (M.mulVec h) / S - 1 = d M := by
      show _ = 1 / S * (normSq (M.mulVec h) - S)
      field_simp
    rw [hdx] at h1
    have h2 : nrm (M.mulVec h) = c * √(normSq (M.mulVec h) / S) := by
      rw [← hcS, ← Real.sqrt_mul hS.le]
      unfold nrm
      congr 1
      field_simp
    have h3 : |d M| ^ 3 = |d M| * |d M ^ 2| := by rw [abs_pow]; ring
    rw [h2]
    have h4 := mul_le_mul_of_nonneg_left h1 hc0
    rw [h3] at h4
    linarith
  have hmono := integral_mono iL hi hpt
  rw [eL, ed1, ed2] at hmono
  refine le_trans ?_ hmono
  have hr : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm'
  have h5 : 3 * c / 8 * ∫ M, |d M| * |d M ^ 2| ∂gaussMat m k v ≤
      3 * c / 8 * (√2 / √(m : ℝ) * (K4 m / (m : ℝ))) :=
    mul_le_mul_of_nonneg_left e3 (by positivity)
  have h6 : c * (1 - dChi m) = c / 2 * 0 + c - c / 8 * (2 / (m : ℝ)) -
      3 * c / 8 * (√2 / √(m : ℝ) * (K4 m / (m : ℝ))) := by
    unfold dChi
    field_simp
    ring
  rw [h6]
  linarith

/-- `E|h₂(z)| ≥ √(m/k)·|z|·(1 − epsW m/2)` for the hidden map of a random MLP. -/
lemma hid2_nrm_mean_lower {k m : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (z : Fin k → ℝ) :
    Integrable (fun θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      nrm (hid2 θ.1 θ.2 z)) ((gaussMat m k (2 / (k : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) ∧
    √((m : ℝ) / k) * nrm z * (1 - epsW m / 2) ≤
      ∫ θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ, nrm (hid2 θ.1 θ.2 z)
        ∂((gaussMat m k (2 / (k : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨i2, e2⟩ := hid2_sq (m₁ := m) (m₂ := m) (two_div_nonneg k) (two_div_nonneg m) z
  obtain ⟨i4, e4⟩ := hid2_four (m₁ := m) (m₂ := m) (two_div_nonneg k) (two_div_nonneg m) z
  have mns : Measurable (fun θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      normSq (hid2 θ.1 θ.2 z)) := (continuous_normSq.comp (continuous_hid2_param z)).measurable
  have mnr : Measurable (fun θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      nrm (hid2 θ.1 θ.2 z)) := (continuous_nrm.comp (continuous_hid2_param z)).measurable
  have hi : Integrable (fun θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      nrm (hid2 θ.1 θ.2 z)) ((gaussMat m k (2 / (k : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) := by
    refine integrable_of_sq mnr (fun θ => nrm_nonneg _) ?_
    have : (fun θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        nrm (hid2 θ.1 θ.2 z) ^ 2) = fun θ => normSq (hid2 θ.1 θ.2 z) := funext fun θ => nrm_sq _
    rw [this]
    exact i2
  refine ⟨hi, ?_⟩
  have hint0 : 0 ≤ ∫ θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ,
      nrm (hid2 θ.1 θ.2 z) ∂((gaussMat m k (2 / (k : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) :=
    integral_nonneg fun θ => nrm_nonneg _
  by_cases hz : normSq z = 0
  · rw [nrm_zero_of hz]
    simpa using hint0
  have hzp : 0 < normSq z := lt_of_le_of_ne (normSq_nonneg z) (Ne.symm hz)
  have hS : 0 < (m : ℝ) / k * normSq z := by positivity
  set S := (m : ℝ) / k * normSq z with hSdef
  have e2' : ∫ θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ,
      normSq (hid2 θ.1 θ.2 z) ∂((gaussMat m k (2 / (k : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) =
      S := by
    rw [e2, hSdef]; field_simp
  have e4' : ∫ θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ,
      normSq (hid2 θ.1 θ.2 z) ^ 2
      ∂((gaussMat m k (2 / (k : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) =
      S ^ 2 * (1 + epsW m) := by
    rw [e4, hSdef]; unfold epsW; field_simp; ring
  have hc : √((m : ℝ) / k) * nrm z = √S := by
    unfold nrm
    rw [← Real.sqrt_mul (by positivity)]
  rw [hc]
  obtain ⟨c, hc0, hcS⟩ : ∃ c : ℝ, 0 ≤ c ∧ √S = c := ⟨√S, Real.sqrt_nonneg _, rfl⟩
  rw [hcS]
  have iL : Integrable (fun θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      c * (3 / (2 * S)) * normSq (hid2 θ.1 θ.2 z) - c / (2 * S ^ 2) * normSq (hid2 θ.1 θ.2 z) ^ 2)
      ((gaussMat m k (2 / (k : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) :=
    (i2.const_mul _).sub (i4.const_mul _)
  have hpt : ∀ θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ,
      c * (3 / (2 * S)) * normSq (hid2 θ.1 θ.2 z) -
        c / (2 * S ^ 2) * normSq (hid2 θ.1 θ.2 z) ^ 2 ≤ nrm (hid2 θ.1 θ.2 z) := by
    intro θ
    have hx : 0 ≤ normSq (hid2 θ.1 θ.2 z) / S := div_nonneg (normSq_nonneg _) hS.le
    have h1 := sqrt_ge_quad' hx
    have h2 : nrm (hid2 θ.1 θ.2 z) = c * √(normSq (hid2 θ.1 θ.2 z) / S) := by
      rw [← hcS, ← Real.sqrt_mul hS.le]
      unfold nrm
      congr 1
      field_simp
    rw [h2]
    have h4 := mul_le_mul_of_nonneg_left h1 hc0
    refine le_trans (le_of_eq ?_) h4
    field_simp
    ring
  have hmono := integral_mono iL hi hpt
  rw [integral_sub (i2.const_mul _) (i4.const_mul _), integral_const_mul, integral_const_mul,
    e2', e4'] at hmono
  refine le_trans (le_of_eq ?_) hmono
  field_simp
  ring

/-- A whole network: `E|N(z)| ≥ √(2q/k)·|z|·(1 − dChi q)·(1 − epsW m / 2)` if `dChi q ≤ 1`. -/
theorem mlp_nrm_mean_lower {k m q : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hd : dChi q ≤ 1) (z : Fin k → ℝ) :
    √(2 * (q : ℝ) / k) * nrm z * ((1 - dChi q) * (1 - epsW m / 2)) ≤
      ∫ θ : MlpParam k m q, nrm (mlpEval θ z) ∂mlpGauss k m q := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hf := (mlp_nrm_single (q := q) hm z).1
  unfold mlpGauss at hf ⊢
  obtain ⟨hi, hl⟩ := hid2_nrm_mean_lower hm hk z
  have hg : Integrable (fun θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      √((q : ℝ) * (2 / (m : ℝ))) * nrm (hid2 θ.1 θ.2 z) * (1 - dChi q))
      ((gaussMat m k (2 / (k : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) :=
    (hi.const_mul _).mul_const _
  have key := integral_assoc_ge (gaussMat m k (2 / (k : ℝ))) (gaussMat m m (2 / (m : ℝ)))
    (gaussMat q m (2 / (m : ℝ))) hf hg
    (fun a b => (lin_nrm_mean_lower (m := q) (two_div_nonneg m) hq (hid2 a b z)).2)
  refine le_trans ?_ key
  have e : ∫ θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ,
      √((q : ℝ) * (2 / (m : ℝ))) * nrm (hid2 θ.1 θ.2 z) * (1 - dChi q)
      ∂((gaussMat m k (2 / (k : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) =
      √((q : ℝ) * (2 / (m : ℝ))) * (∫ θ : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ,
        nrm (hid2 θ.1 θ.2 z)
        ∂((gaussMat m k (2 / (k : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))) * (1 - dChi q) := by
    rw [integral_mul_const, integral_const_mul]
  rw [e]
  have hsq : √(2 * (q : ℝ) / k) = √((q : ℝ) * (2 / (m : ℝ))) * √((m : ℝ) / k) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [hsq]
  have h1 : 0 ≤ √((q : ℝ) * (2 / (m : ℝ))) := Real.sqrt_nonneg _
  have h2 : 0 ≤ 1 - dChi q := by linarith
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl h1) h2
  refine le_trans (le_of_eq ?_) h3
  ring

end BstLean.Part133

open BstLean.Part133 in
#print axioms persp_le3
open BstLean.Part133 in
#print axioms lin_layer_L2r
open BstLean.Part133 in
#print axioms lin_layer_L2s
open BstLean.Part133 in
#print axioms lin_nrm_mean_lower
open BstLean.Part133 in
#print axioms mlp_nrm_mean_lower
