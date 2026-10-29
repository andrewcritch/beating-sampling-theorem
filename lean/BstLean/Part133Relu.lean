import BstLean.Part133L2
import BstLean.Part133Four

/-!
# Part 133, item 3 (links): `L²` bounds of one layer and of a whole network

Role: `delegations/statements/p133-spec.md`. Paper source: `onW4c-cx.md` §4 (links `F`, `A_3`,
`A_2`, `A_1`), with the Lipschitz bound T2(3)(ii) of the perspective function.

* `L2le.add0`: the triangle inequality with bounds `≥ 0`.
* `psi_abs_sub`: `|Ψ_G(y, y′) − p̄·G(t)| ≤ G(0)·||y||y′| − p̄| + |⟨y, y′⟩ − p̄·t|`.
* `relu_layer_L2`: `‖Ψ_G(ReLU(Mh), ReLU(Mh′)) − (m/2)v·Ψ_{G∘κ}(h, h′)‖₂ ≤
  ((5·G(0) + √6)/√m)·(m/2)v·|h||h′|`.
* `lin_layer_L2`: `‖Ψ_G(Mh, Mh′) − mv·Ψ_G(h, h′)‖₂ ≤ ((√10·G(0) + √2)/√m)·mv·|h||h′|`.
* `hid2_dot_L2`, `KF_L2`: the two hidden layers (of `F`).
* `mlp_psi_L2`: a whole random ReLU MLP.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part133

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  uniformSphere_moments)
open BstLean.Part130 BstLean.Part131 BstLean.Part132

/-! ## Abstract tools -/

section abstract

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The triangle inequality in `L²` with bounds `≥ 0`. -/
theorem L2le.add0 {f g : Ω → ℝ} {a b : ℝ} (hf : L2le μ f a) (hg : L2le μ g b) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : L2le μ (fun ω => f ω + g ω) (a + b) := by
  have h1 : ∀ ε : ℝ, 0 < ε → L2le μ (fun ω => f ω + g ω) (a + ε + (b + ε)) := fun ε hε =>
    (hf.mono ha (by linarith)).add (hg.mono hb (by linarith)) (by linarith) (by linarith)
  have h0 := h1 1 one_pos
  refine ⟨h0.1, h0.2.1, ?_⟩
  have hs : √(∫ ω, (f ω + g ω) ^ 2 ∂μ) ≤ a + b := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h2 := (h1 (ε / 2) (by positivity)).le
    rw [Real.sqrt_le_left (by linarith)]
    refine h2.trans (le_of_eq ?_)
    ring
  exact (Real.sqrt_le_left (by linarith)).1 hs

variable {ι : Type*} [Fintype ι]

/-- The Lipschitz bound of the perspective function, in both directions. -/
lemma psi_abs_sub {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) {pb t : ℝ} (hpb : 0 ≤ pb)
    (ht : |t| ≤ 1) :
    |psi G y y' - pb * G t| ≤ G 0 * |nrm y * nrm y' - pb| + |dotp y y' - pb * t| := by
  have hcb : |pb * t| ≤ pb := by
    rw [abs_mul, abs_of_nonneg hpb]
    nlinarith
  have up := psi_le hG y y' hpb hcb
  rw [persp_mul] at up
  have lo : pb * G t ≤ psi G y y' + G 0 * |pb - nrm y * nrm y'| + |pb * t - dotp y y'| := by
    have := persp_le hG hpb hcb (nrm_mul_nonneg y y') (abs_dotp_le_nrm y y')
    rw [persp_mul] at this
    exact this
  rw [abs_sub_comm pb, abs_sub_comm (pb * t)] at lo
  rw [abs_le]
  constructor <;> linarith

/-- From `L²` bounds of the norm product and of the inner product to an `L²` bound of `Ψ_G`. -/
lemma psi_L2_core {G : ℝ → ℝ} (hG : KGood G) {Y Y' : Ω → ι → ℝ}
    (hm : AEStronglyMeasurable (fun ω => psi G (Y ω) (Y' ω)) μ) {pb t a b : ℝ} (hpb : 0 ≤ pb)
    (ht : |t| ≤ 1) (hP : L2le μ (fun ω => nrm (Y ω) * nrm (Y' ω) - pb) a)
    (hC : L2le μ (fun ω => dotp (Y ω) (Y' ω) - pb * t) b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    L2le μ (fun ω => psi G (Y ω) (Y' ω) - pb * G t) (G 0 * a + b) := by
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have hP1 : L2le μ (fun ω => |nrm (Y ω) * nrm (Y' ω) - pb|) a :=
    L2le.of_abs_le (continuous_abs.comp_aestronglyMeasurable hP.aesm) hP
      (fun ω => le_of_eq (abs_abs _))
  have hC1 : L2le μ (fun ω => |dotp (Y ω) (Y' ω) - pb * t|) b :=
    L2le.of_abs_le (continuous_abs.comp_aestronglyMeasurable hC.aesm) hC
      (fun ω => le_of_eq (abs_abs _))
  have hsum := (hP1.const_mul_nonneg hG0).add0 hC1 (mul_nonneg hG0 ha) hb
  refine L2le.of_abs_le (hm.sub aestronglyMeasurable_const) hsum (fun ω => ?_)
  rw [abs_of_nonneg (add_nonneg (mul_nonneg hG0 (abs_nonneg _)) (abs_nonneg _))]
  exact psi_abs_sub hG (Y ω) (Y' ω) hpb ht

end abstract

variable {m k : ℕ}

/-! ## One layer -/

/-- **One ReLU layer in `L²`.** -/
theorem relu_layer_L2 {G : ℝ → ℝ} (hG : KGood G) {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m)
    (h h' : Fin k → ℝ) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => psi G (reluV (M.mulVec h)) (reluV (M.mulVec h')) -
        (m : ℝ) / 2 * v * psi (G ∘ kappa) h h')
      ((5 * G 0 + √6) / √(m : ℝ) * ((m : ℝ) / 2 * v * (nrm h * nrm h'))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set pb : ℝ := (m : ℝ) / 2 * v * (nrm h * nrm h') with hpb
  have hpb0 : 0 ≤ pb := mul_nonneg (by positivity) (nrm_mul_nonneg h h')
  set t := kappa (cosv h h') with ht
  have ht01 := kappa_mem (cosv_mem h h').1 (cosv_mem h h').2
  have htabs : |t| ≤ 1 := by rw [abs_of_nonneg ht01.1]; exact ht01.2
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
  have hP : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) - pb) (5 / √(m : ℝ) * pb) := by
    have e : (5 / √(m : ℝ) * pb) ^ 2 = 25 / (m : ℝ) * pb ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hm'.le]; norm_num
    exact L2le.mk' mP.aestronglyMeasurable iP2 (uP2.trans (le_of_eq e.symm))
  have hC : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - pb * t) (√6 / √(m : ℝ) * pb) := by
    refine L2le.mk' mC.aestronglyMeasurable iC2 (uC2.trans (le_of_eq ?_))
    rw [mul_pow, div_pow, Real.sq_sqrt hm'.le, Real.sq_sqrt (by norm_num), hpb, ← nrm_sq h,
      ← nrm_sq h']
    field_simp
    ring
  have key := psi_L2_core (μ := gaussMat m k v) hG
    (Y := fun M : Matrix (Fin m) (Fin k) ℝ => reluV (M.mulVec h))
    (Y' := fun M : Matrix (Fin m) (Fin k) ℝ => reluV (M.mulVec h'))
    (measurable_psi_relu hG.cont h h').aestronglyMeasurable hpb0 htabs hP hC
    (by positivity) (by positivity)
  have e1 : (m : ℝ) / 2 * v * psi (G ∘ kappa) h h' = pb * G t := by
    rw [hpb, ht]; unfold psi; simp only [Function.comp]; ring
  rw [e1]
  refine key.congr_bound ?_
  ring

/-- **One linear layer in `L²`.** -/
theorem lin_layer_L2 {G : ℝ → ℝ} (hG : KGood G) {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m)
    (h h' : Fin k → ℝ) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => psi G (M.mulVec h) (M.mulVec h') -
        (m : ℝ) * v * psi G h h')
      ((√10 * G 0 + √2) / √(m : ℝ) * ((m : ℝ) * v * (nrm h * nrm h'))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set pb : ℝ := (m : ℝ) * v * (nrm h * nrm h') with hpb
  have hpb0 : 0 ≤ pb := mul_nonneg (by positivity) (nrm_mul_nonneg h h')
  set t := cosv h h' with ht
  have htabs : |t| ≤ 1 := abs_le.2 (cosv_mem h h')
  obtain ⟨-, -, -, iP2, uP2⟩ := lin_layer_pair (m := m) hv hm h h'
  obtain ⟨iC2, -⟩ := lin_dot_var0 (m := m) hv h h'
  have uC2 := lin_dot_var (m := m) hv h h'
  have ec : (m : ℝ) * (v * dotp h h') = pb * t := by
    rw [dotp_eq_cosv_mul h h', hpb, ht]; ring
  rw [ec] at iC2 uC2
  rw [← hpb] at iP2 uP2
  have mP : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      nrm (M.mulVec h) * nrm (M.mulVec h') - pb) :=
    (((continuous_nrm.measurable.comp (measurable_mulVec_right h)).mul
      (continuous_nrm.measurable.comp (measurable_mulVec_right h'))).sub measurable_const)
  have mC : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dotp (M.mulVec h) (M.mulVec h') - pb * t) :=
    (measurable_dotp_comp (measurable_mulVec_right h) (measurable_mulVec_right h')).sub
      measurable_const
  have hP : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      nrm (M.mulVec h) * nrm (M.mulVec h') - pb) (√10 / √(m : ℝ) * pb) := by
    have e : (√10 / √(m : ℝ) * pb) ^ 2 = 10 / (m : ℝ) * pb ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hm'.le, Real.sq_sqrt (by norm_num)]
    exact L2le.mk' mP.aestronglyMeasurable iP2 (uP2.trans (le_of_eq e.symm))
  have hd : dotp h h' ^ 2 ≤ normSq h * normSq h' := by
    have := abs_dotp_le_nrm h h'
    have h2 : dotp h h' ^ 2 ≤ (nrm h * nrm h') ^ 2 := by
      rw [← sq_abs (dotp h h')]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    rwa [mul_pow, nrm_sq, nrm_sq] at h2
  have hC : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dotp (M.mulVec h) (M.mulVec h') - pb * t) (√2 / √(m : ℝ) * pb) := by
    refine L2le.mk' mC.aestronglyMeasurable iC2 (uC2.le.trans ?_)
    rw [mul_pow, div_pow, Real.sq_sqrt hm'.le, Real.sq_sqrt (by norm_num), hpb, mul_pow, mul_pow,
      mul_pow, nrm_sq, nrm_sq]
    have h3 : (m : ℝ) * v ^ 2 * (normSq h * normSq h' + dotp h h' ^ 2) ≤
        (m : ℝ) * v ^ 2 * (2 * (normSq h * normSq h')) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    refine h3.trans (le_of_eq ?_)
    field_simp
  have key := psi_L2_core (μ := gaussMat m k v) hG
    (Y := fun M : Matrix (Fin m) (Fin k) ℝ => M.mulVec h)
    (Y' := fun M : Matrix (Fin m) (Fin k) ℝ => M.mulVec h')
    (measurable_psi_lin hG.cont h h').aestronglyMeasurable hpb0 htabs hP hC
    (by positivity) (by positivity)
  have e1 : (m : ℝ) * v * psi G h h' = pb * G t := by
    rw [hpb, ht]; unfold psi; ring
  rw [e1]
  refine key.congr_bound ?_
  ring

/-- The `L²` norm of the product of the two norms after a ReLU layer. -/
theorem relu_nrm_L2 {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m) (h h' : Fin k → ℝ) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')))
      (√(1 + 5 / (m : ℝ)) * ((m : ℝ) / 2 * v * (nrm h * nrm h'))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmeas : ∀ h : Fin k → ℝ, Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      normSq (reluV (M.mulVec h))) := fun h =>
    measurable_normSq.comp (measurable_reluV.comp (measurable_mulVec_right h))
  have mF : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h'))) :=
    (continuous_nrm.measurable.comp (measurable_reluV.comp (measurable_mulVec_right h))).mul
      (continuous_nrm.measurable.comp (measurable_reluV.comp (measurable_mulVec_right h')))
  obtain ⟨iU, uU⟩ := integral_mul_le_sqrt (μ := gaussMat m k v) (hmeas h) (hmeas h')
    (layer_relu_four hv h).1 (layer_relu_four hv h').1
  have s : ∀ h : Fin k → ℝ, √(∫ M : Matrix (Fin m) (Fin k) ℝ,
      normSq (reluV (M.mulVec h)) ^ 2 ∂gaussMat m k v) =
      √(1 + 5 / (m : ℝ)) * ((m : ℝ) / 2 * (v * normSq h)) := by
    intro h
    rw [(layer_relu_four hv h).2]
    have e : ((m : ℝ) ^ 2 / 4 + 5 * m / 4) * (v * normSq h) ^ 2 =
        (1 + 5 / (m : ℝ)) * ((m : ℝ) / 2 * (v * normSq h)) ^ 2 := by
      field_simp; ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by have := normSq_nonneg h; positivity)]
  refine L2le.of_sq_le mF.aestronglyMeasurable iU (fun M => ?_) (uU.trans (le_of_eq ?_))
  · rw [mul_pow, nrm_sq, nrm_sq, abs_of_nonneg (normSq_nonneg _), abs_of_nonneg (normSq_nonneg _)]
  · rw [s h, s h', mul_pow, Real.sq_sqrt (by positivity), ← nrm_sq h, ← nrm_sq h']
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 + 5 / (m : ℝ) by positivity)
    calc √(1 + 5 / (m : ℝ)) * ((m : ℝ) / 2 * (v * nrm h ^ 2)) *
          (√(1 + 5 / (m : ℝ)) * ((m : ℝ) / 2 * (v * nrm h' ^ 2)))
        = (√(1 + 5 / (m : ℝ)) * √(1 + 5 / (m : ℝ))) *
          ((m : ℝ) / 2 * v * (nrm h * nrm h')) ^ 2 := by ring
      _ = _ := by rw [this]

variable {m₁ m₂ q : ℕ}

/-! ## Two hidden layers -/

/-- **The two hidden layers in `L²`.** -/
theorem hid2_dot_L2 {v₁ v₂ : ℝ} (h₁ : 0 ≤ v₁) (h₂ : 0 ≤ v₂) (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (y y' : Fin k → ℝ) :
    L2le ((gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂))
      (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
        dotp (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y') -
          (m₂ : ℝ) / 2 * v₂ * ((m₁ : ℝ) / 2 * v₁ * psi (kappa ∘ kappa) y y'))
      ((√6 * √(1 + 5 / (m₁ : ℝ)) / √(m₂ : ℝ) + (5 * kappa 0 + √6) / √(m₁ : ℝ)) *
        ((m₂ : ℝ) / 2 * v₂ * ((m₁ : ℝ) / 2 * v₁ * (nrm y * nrm y')))) := by
  have hm₁' : (0 : ℝ) < m₁ := by exact_mod_cast hm₁
  have hm₂' : (0 : ℝ) < m₂ := by exact_mod_cast hm₂
  have hk0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  have hc2 : 0 ≤ (m₂ : ℝ) / 2 * v₂ := by positivity
  have hnn := nrm_mul_nonneg y y'
  -- the residual of the last layer
  have mA : Measurable (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
      dotp (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y') -
        (m₂ : ℝ) / 2 * v₂ * psi kappa (reluV (θ.1.mulVec y)) (reluV (θ.1.mulVec y'))) :=
    (continuous_dotp.comp ((continuous_hid2_param y).prodMk
      (continuous_hid2_param y'))).measurable.sub
      (((measurable_psi_relu continuous_kappa y y').comp measurable_fst).const_mul _)
  have hgA : L2le (gaussMat m₁ k v₁) (fun M₁ : Matrix (Fin m₁) (Fin k) ℝ =>
      √6 / √(m₂ : ℝ) * ((m₂ : ℝ) / 2 * v₂ *
        (nrm (reluV (M₁.mulVec y)) * nrm (reluV (M₁.mulVec y')))))
      (√6 / √(m₂ : ℝ) * ((m₂ : ℝ) / 2 * v₂ *
        (√(1 + 5 / (m₁ : ℝ)) * ((m₁ : ℝ) / 2 * v₁ * (nrm y * nrm y'))))) :=
    ((relu_nrm_L2 (m := m₁) h₁ hm₁ y y').const_mul_nonneg hc2).const_mul_nonneg (by positivity)
  have hA : L2le ((gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂))
      (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
        dotp (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y') -
          (m₂ : ℝ) / 2 * v₂ * psi kappa (reluV (θ.1.mulVec y)) (reluV (θ.1.mulVec y')))
      (√6 / √(m₂ : ℝ) * ((m₂ : ℝ) / 2 * v₂ *
        (√(1 + 5 / (m₁ : ℝ)) * ((m₁ : ℝ) / 2 * v₁ * (nrm y * nrm y'))))) := by
    refine L2le.prod mA.aestronglyMeasurable hgA (Filter.Eventually.of_forall fun M₁ => ?_)
    obtain ⟨iC, uC⟩ := layer_dot_relu_var (m := m₂) h₂ (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y'))
    have e : (m₂ : ℝ) / 2 * (v₂ * kernelPhi (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y'))) =
        (m₂ : ℝ) / 2 * v₂ * psi kappa (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y')) := by
      rw [kernelPhi_eq_psi]; ring
    rw [e] at iC uC
    refine ⟨iC, uC.trans (le_of_eq ?_)⟩
    rw [mul_pow, div_pow, Real.sq_sqrt hm₂'.le, Real.sq_sqrt (by norm_num), mul_pow, mul_pow,
      mul_pow, nrm_sq, nrm_sq]
    field_simp
    ring
  -- the first layer
  have hB : L2le ((gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂))
      (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
        (m₂ : ℝ) / 2 * v₂ * (psi kappa (reluV (θ.1.mulVec y)) (reluV (θ.1.mulVec y')) -
          (m₁ : ℝ) / 2 * v₁ * psi (kappa ∘ kappa) y y'))
      ((m₂ : ℝ) / 2 * v₂ * ((5 * kappa 0 + √6) / √(m₁ : ℝ) *
        ((m₁ : ℝ) / 2 * v₁ * (nrm y * nrm y')))) :=
    ((relu_layer_L2 (m := m₁) kGood_kappa h₁ hm₁ y y').const_mul_nonneg hc2).comp_fst
  have hsum := hA.add0 hB (by positivity) (by positivity)
  refine (hsum.congr_fun fun θ => ?_).congr_bound ?_
  · ring
  · field_simp

variable {n mF : ℕ}

/-- The constant of the `F` links. -/
noncomputable def cF2 (mF : ℕ) : ℝ :=
  √6 * √(1 + 5 / (mF : ℝ)) / √(mF : ℝ) + (5 * kappa 0 + √6) / √(mF : ℝ)

/-- **The two hidden layers of `F` in `L²`** (links `F_2`, `F_1`). -/
theorem KF_L2 (hn : 1 ≤ n) (hmF : 1 ≤ mF) (y y' : Fin n → ℝ) :
    L2le (mlpGauss n mF 1)
      (fun F : MlpParam n mF 1 => 2 / (mF : ℝ) * dotp (hid2 F.1 F.2.1 y) (hid2 F.1 F.2.1 y') -
        2 / (n : ℝ) * psi (kappa ∘ kappa) y y')
      (cF2 mF * (2 / (n : ℝ) * (nrm y * nrm y'))) := by
  have hmF' : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 := (hid2_dot_L2 (m₁ := mF) (m₂ := mF) (two_div_nonneg n) (two_div_nonneg mF) hmF hmF
    y y').const_mul_nonneg (show (0 : ℝ) ≤ 2 / (mF : ℝ) by positivity)
  have h1 := h0.comp_map (P := mlpGauss n mF 1)
    (φ := fun θ : MlpParam n mF 1 => (θ.1, θ.2.1)) (by fun_prop) (by unfold mlpGauss; exact map_drop3)
  refine (h1.congr_fun fun F => ?_).congr_bound ?_
  · field_simp
  · unfold cF2
    field_simp

/-! ## A whole network -/

/-- The last two matrices, for fixed first hidden vectors `g, g′`, in `L²`. -/
theorem tail_psi_L2 {G : ℝ → ℝ} (hG : KGood G) {v₂ v₃ : ℝ} (h₂ : 0 ≤ v₂) (h₃ : 0 ≤ v₃)
    (hm₂ : 1 ≤ m₂) (hq : 1 ≤ q) (g g' : Fin m₁ → ℝ) :
    L2le ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃))
      (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        psi G (θ.2.mulVec (reluV (θ.1.mulVec g))) (θ.2.mulVec (reluV (θ.1.mulVec g'))) -
          (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂ * psi (G ∘ kappa) g g'))
      (((√10 * G 0 + √2) / √(q : ℝ) * √(1 + 5 / (m₂ : ℝ)) + (5 * G 0 + √6) / √(m₂ : ℝ)) *
        ((q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂ * (nrm g * nrm g')))) := by
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have hc3 : 0 ≤ (q : ℝ) * v₃ := by positivity
  have hnn := nrm_mul_nonneg g g'
  have hmeas : Measurable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
      psi G (θ.2.mulVec (reluV (θ.1.mulVec g))) (θ.2.mulVec (reluV (θ.1.mulVec g')))) := by
    have c : ∀ g : Fin m₁ → ℝ, Continuous (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ ×
        Matrix (Fin q) (Fin m₂) ℝ => θ.2.mulVec (reluV (θ.1.mulVec g))) := fun g =>
      Continuous.matrix_mulVec continuous_snd
        (continuous_reluV.comp (Continuous.matrix_mulVec continuous_fst continuous_const))
    exact Measurable.comp (g := fun p : (Fin q → ℝ) × (Fin q → ℝ) => psi G p.1 p.2)
      (f := fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        (θ.2.mulVec (reluV (θ.1.mulVec g)), θ.2.mulVec (reluV (θ.1.mulVec g'))))
      (measurable_psi hG.cont) ((c g).prodMk (c g')).measurable
  have mA : Measurable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
      psi G (θ.2.mulVec (reluV (θ.1.mulVec g))) (θ.2.mulVec (reluV (θ.1.mulVec g'))) -
        (q : ℝ) * v₃ * psi G (reluV (θ.1.mulVec g)) (reluV (θ.1.mulVec g'))) :=
    hmeas.sub (((measurable_psi_relu hG.cont g g').comp measurable_fst).const_mul _)
  have hgA : L2le (gaussMat m₂ m₁ v₂) (fun M₂ : Matrix (Fin m₂) (Fin m₁) ℝ =>
      (√10 * G 0 + √2) / √(q : ℝ) * ((q : ℝ) * v₃ *
        (nrm (reluV (M₂.mulVec g)) * nrm (reluV (M₂.mulVec g')))))
      ((√10 * G 0 + √2) / √(q : ℝ) * ((q : ℝ) * v₃ *
        (√(1 + 5 / (m₂ : ℝ)) * ((m₂ : ℝ) / 2 * v₂ * (nrm g * nrm g'))))) :=
    ((relu_nrm_L2 (m := m₂) h₂ hm₂ g g').const_mul_nonneg hc3).const_mul_nonneg (by positivity)
  have hA : L2le ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃))
      (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        psi G (θ.2.mulVec (reluV (θ.1.mulVec g))) (θ.2.mulVec (reluV (θ.1.mulVec g'))) -
          (q : ℝ) * v₃ * psi G (reluV (θ.1.mulVec g)) (reluV (θ.1.mulVec g')))
      ((√10 * G 0 + √2) / √(q : ℝ) * ((q : ℝ) * v₃ *
        (√(1 + 5 / (m₂ : ℝ)) * ((m₂ : ℝ) / 2 * v₂ * (nrm g * nrm g'))))) :=
    L2le.prod' mA.aestronglyMeasurable hgA (Filter.Eventually.of_forall fun M₂ =>
      lin_layer_L2 (m := q) hG h₃ hq (reluV (M₂.mulVec g)) (reluV (M₂.mulVec g')))
  have hB : L2le ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃))
      (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        (q : ℝ) * v₃ * (psi G (reluV (θ.1.mulVec g)) (reluV (θ.1.mulVec g')) -
          (m₂ : ℝ) / 2 * v₂ * psi (G ∘ kappa) g g'))
      ((q : ℝ) * v₃ * ((5 * G 0 + √6) / √(m₂ : ℝ) *
        ((m₂ : ℝ) / 2 * v₂ * (nrm g * nrm g')))) :=
    ((relu_layer_L2 (m := m₂) hG h₂ hm₂ g g').const_mul_nonneg hc3).comp_fst
  have hsum := hA.add0 hB (by positivity) (by positivity)
  refine (hsum.congr_fun fun θ => ?_).congr_bound ?_
  · ring
  · ring

/-- The constant of the links of a whole network. -/
noncomputable def cA (G : ℝ → ℝ) (m q : ℕ) : ℝ :=
  (√10 * G 0 + √2) / √(q : ℝ) * (1 + 5 / (m : ℝ)) +
    (5 * G 0 + √6) / √(m : ℝ) * √(1 + 5 / (m : ℝ)) + (5 + √6) / √(m : ℝ)

/-- **A whole random ReLU MLP in `L²`** (links `A_3`, `A_2`, `A_1`). -/
theorem mlp_psi_L2 {G : ℝ → ℝ} (hG : KGood G) {m : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (z z' : Fin k → ℝ) :
    L2le (mlpGauss k m q)
      (fun θ : MlpParam k m q => psi G (mlpEval θ z) (mlpEval θ z') -
        2 * (q : ℝ) / k * psi (G ∘ kappa ∘ kappa) z z')
      (cA G m q * (2 * (q : ℝ) / k * (nrm z * nrm z'))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have hGk := hG.comp_kappa
  have hGk0 : 0 ≤ (G ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have hGk1 : (G ∘ kappa) 0 ≤ 1 := hGk.le_one KGood.zero_mem
  have h1 : (0 : ℝ) ≤ 2 / (k : ℝ) := two_div_nonneg k
  have h2 : (0 : ℝ) ≤ 2 / (m : ℝ) := two_div_nonneg m
  have hnn := nrm_mul_nonneg z z'
  set K : ℝ := (√10 * G 0 + √2) / √(q : ℝ) * √(1 + 5 / (m : ℝ)) + (5 * G 0 + √6) / √(m : ℝ)
    with hK
  have hK0 : 0 ≤ K := by positivity
  set c3 : ℝ := (q : ℝ) * (2 / (m : ℝ)) with hc3
  set c2 : ℝ := (m : ℝ) / 2 * (2 / (m : ℝ)) with hc2
  have hc30 : 0 ≤ c3 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have mA : Measurable (fun θ : MlpParam k m q =>
      psi G (mlpEval θ z) (mlpEval θ z') -
        c3 * (c2 * psi (G ∘ kappa) (reluV (θ.1.mulVec z)) (reluV (θ.1.mulVec z')))) :=
    (measurable_psi_mlp hG.cont z z').sub
      ((((measurable_psi_relu hGk.cont z z').comp measurable_fst).const_mul _).const_mul _)
  have hgA : L2le (gaussMat m k (2 / (k : ℝ))) (fun M₁ : Matrix (Fin m) (Fin k) ℝ =>
      K * (c3 * (c2 * (nrm (reluV (M₁.mulVec z)) * nrm (reluV (M₁.mulVec z'))))))
      (K * (c3 * (c2 * (√(1 + 5 / (m : ℝ)) *
        ((m : ℝ) / 2 * (2 / (k : ℝ)) * (nrm z * nrm z')))))) :=
    (((relu_nrm_L2 (m := m) h1 hm z z').const_mul_nonneg hc20).const_mul_nonneg
      hc30).const_mul_nonneg hK0
  have hA : L2le (mlpGauss k m q) (fun θ : MlpParam k m q =>
      psi G (mlpEval θ z) (mlpEval θ z') -
        c3 * (c2 * psi (G ∘ kappa) (reluV (θ.1.mulVec z)) (reluV (θ.1.mulVec z'))))
      (K * (c3 * (c2 * (√(1 + 5 / (m : ℝ)) *
        ((m : ℝ) / 2 * (2 / (k : ℝ)) * (nrm z * nrm z')))))) := by
    unfold mlpGauss at mA ⊢
    exact L2le.prod' mA.aestronglyMeasurable hgA (Filter.Eventually.of_forall fun M₁ =>
      tail_psi_L2 (m₂ := m) (q := q) hG h2 h2 hm hq (reluV (M₁.mulVec z))
        (reluV (M₁.mulVec z')))
  have hB0 : L2le (gaussMat m k (2 / (k : ℝ))) (fun M₁ : Matrix (Fin m) (Fin k) ℝ =>
      c3 * (c2 * (psi (G ∘ kappa) (reluV (M₁.mulVec z)) (reluV (M₁.mulVec z')) -
        (m : ℝ) / 2 * (2 / (k : ℝ)) * psi ((G ∘ kappa) ∘ kappa) z z')))
      (c3 * (c2 * ((5 + √6) / √(m : ℝ) * ((m : ℝ) / 2 * (2 / (k : ℝ)) * (nrm z * nrm z'))))) := by
    refine ((((relu_layer_L2 (m := m) hGk h1 hm z z').mono (by positivity) ?_).const_mul_nonneg
      hc20).const_mul_nonneg hc30)
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    linarith
  have hB : L2le (mlpGauss k m q) (fun θ : MlpParam k m q =>
      c3 * (c2 * (psi (G ∘ kappa) (reluV (θ.1.mulVec z)) (reluV (θ.1.mulVec z')) -
        (m : ℝ) / 2 * (2 / (k : ℝ)) * psi ((G ∘ kappa) ∘ kappa) z z')))
      (c3 * (c2 * ((5 + √6) / √(m : ℝ) * ((m : ℝ) / 2 * (2 / (k : ℝ)) * (nrm z * nrm z'))))) := by
    unfold mlpGauss
    exact hB0.comp_fst
  have hsum := hA.add0 hB (by positivity) (by positivity)
  have hc2e : c2 = 1 := by rw [hc2]; field_simp
  have hcomp : psi (G ∘ kappa ∘ kappa) z z' = psi ((G ∘ kappa) ∘ kappa) z z' := rfl
  refine (hsum.congr_fun fun θ => ?_).congr_bound ?_
  · rw [hcomp, hc2e, hc3]
    field_simp
    ring
  · unfold cA
    rw [hK, hc2e, hc3]
    have hs := Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 + 5 / (m : ℝ) by positivity)
    set s : ℝ := √(1 + 5 / (m : ℝ)) with hsd
    rw [← hs]
    field_simp

end BstLean.Part133

open BstLean.Part133 in
#print axioms relu_layer_L2
open BstLean.Part133 in
#print axioms lin_layer_L2
open BstLean.Part133 in
#print axioms hid2_dot_L2
open BstLean.Part133 in
#print axioms KF_L2
open BstLean.Part133 in
#print axioms mlp_psi_L2
