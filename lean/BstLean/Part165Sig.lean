import BstLean.Part165Poin
import BstLean.Part160Cov8

/-!
# Part 165 (file `Sig`): moments of every even order of the residual scale `σ`

No proof is left open; no `native_decide` or `axiom` is used.

`σ(ξ) = √t·|res_b h(x(ξ))|` (`sigD` of Part 160), `t = 2/m`, `x(ξ) = (c + τξ)/|c + τξ|`.
`X_q = E_ξ[(τ²/|y|²)^q ‖𝒥(x)Π_x‖_op^{2q}]` (`XqN` of Part 160).

* **`sigD_mom`**: `E_ξ|σ − Eσ|^{2q} ≤ (π/2)^{2q}·E|g|^{2q}·t^q·X_q` (`4q + 1 < n`, `q ≥ 1`).
* **`sigD_tail`**: `Pr(|σ − Eσ| ≥ g) ≤ (π/2)^{2q}·E|g|^{2q}·t^q·X_q / g^{2q}`.

This is the input-side part of the paper's Corollary `t7:p06:rotation-singular` with the
gradient bound `|∇_ξ σ| ≤ √t·τ‖𝒥Π‖/|y|` (Part 153's `gradSq_loc_le_sl`).
-/

namespace BstLean.Part165

open MeasureTheory ProbabilityTheory Filter Topology Set Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part148 (EuLip)
open BstLean.Part152 (opN opN_nonneg)
open BstLean.Part153 (nrm jacT cut orthant_sl)
open BstLean.Part160 (sigD phi2D eulip_phi2D XqN)
open BstLean.Part162 (gmom gmom_nonneg)

variable {n : ℕ}

/-- The Lipschitz function of the whole space whose value at a unit vector is `σ`. -/
noncomputable def PhiS (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (b : Fin (mA n) → ℝ) (z : Fin n → ℝ) : ℝ :=
  phi2D b (√(2 / (mA n : ℝ)) • hid2 A₁ A₂ (cut 1 z))

lemma PhiS_lip (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    {b : Fin (mA n) → ℝ} (hb : 0 < normSq b) :
    EuLip (PhiS A₁ A₂ b) (√(2 / (mA n : ℝ)) * (opN A₂ * opN A₁)) := by
  intro z z'
  have hst0 : 0 ≤ √(2 / (mA n : ℝ)) := Real.sqrt_nonneg _
  have hop0 : 0 ≤ opN A₂ * opN A₁ := mul_nonneg (opN_nonneg _) (opN_nonneg _)
  have h1 := eulip_phi2D hb (√(2 / (mA n : ℝ)) • hid2 A₁ A₂ (cut 1 z))
    (√(2 / (mA n : ℝ)) • hid2 A₁ A₂ (cut 1 z'))
  rw [one_mul] at h1
  unfold PhiS
  refine h1.trans ?_
  change nrm (√(2 / (mA n : ℝ)) • hid2 A₁ A₂ (cut 1 z) - √(2 / (mA n : ℝ)) • hid2 A₁ A₂ (cut 1 z'))
    ≤ √(2 / (mA n : ℝ)) * (opN A₂ * opN A₁) * nrm (z - z')
  rw [← smul_sub, BstLean.Part153.nrm_smul, abs_of_nonneg hst0, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hst0
  exact (BstLean.Part153.nrm_hid2_sub_le A₁ A₂ _ _).trans
    (mul_le_mul_of_nonneg_left (BstLean.Part153.nrm_cut_sub_le_sl z z') hop0)

lemma PhiS_sph (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (b : Fin (mA n) → ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (ξ : Fin n → ℝ) : PhiS A₁ A₂ b (sphPt (c + τ • ξ)) = sigD A₁ A₂ c τ b ξ := by
  unfold PhiS
  rw [BstLean.Part153.cut_one_unit_sl (normSq_sphPt hn _)]
  exact (BstLean.Part160.sig_eq_phi2D b _ _).symm

/-- The gradient weight `Γ = t·τ²·‖𝒥Π‖²/|y|²`. -/
noncomputable def GamS (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : ℝ :=
  2 / (mA n : ℝ) * τ ^ 2 * (1 ^ 2 * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
    (normSq (c + τ • ξ))⁻¹))

lemma GamS_nonneg (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : 0 ≤ GamS A₁ A₂ c τ ξ := by
  unfold GamS
  exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
    (mul_nonneg (sq_nonneg _) (inv_nonneg.2 (normSq_nonneg _))))

lemma XqN_nonneg (q : ℕ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) : 0 ≤ XqN q A₁ A₂ c τ :=
  integral_nonneg fun ξ => mul_nonneg (pow_nonneg (mul_nonneg (sq_nonneg _)
    (inv_nonneg.2 (normSq_nonneg _))) _) (pow_nonneg (sq_nonneg _) _)

lemma GamS_pow (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (q : ℕ) (ξ : Fin n → ℝ) :
    √(GamS A₁ A₂ c τ ξ) ^ (2 * q) = (2 / (mA n : ℝ)) ^ q * ((τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q *
      (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2) ^ q) := by
  rw [pow_mul, Real.sq_sqrt (GamS_nonneg A₁ A₂ c τ ξ)]
  unfold GamS
  rw [← mul_pow, ← mul_pow]
  congr 1
  ring

/-- **The moments of even order of `σ`**: `E_ξ|σ − Eσ|^{2q} ≤ (π/2)^{2q}·E|g|^{2q}·t^q·X_q`. -/
theorem sigD_mom {q : ℕ} (hq : 1 ≤ q) (hn : 4 * q + 1 < n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {b : Fin (mA n) → ℝ} (hb : 0 < normSq b) :
    ∫ ξ, |sigD A₁ A₂ c τ b ξ - ∫ ζ, sigD A₁ A₂ c τ b ζ ∂stdGauss (Fin n)| ^ (2 * q)
        ∂stdGauss (Fin n) ≤
      (π / 2) ^ (2 * q) * (gmom (2 * q) * ((2 / (mA n : ℝ)) ^ q * XqN q A₁ A₂ c τ)) := by
  have hn1 : 1 ≤ n := by omega
  have hst0 : 0 ≤ √(2 / (mA n : ℝ)) := Real.sqrt_nonneg _
  have hop0 : 0 ≤ opN A₂ * opN A₁ := mul_nonneg (opN_nonneg _) (opN_nonneg _)
  have hK0 : 0 ≤ √(2 / (mA n : ℝ)) * (opN A₂ * opN A₁) := mul_nonneg hst0 hop0
  have hne := BstLean.Part153.ae_normSq_ne (n := n) hn1 c hτ.ne'
  -- the gradient bound
  have h2 : ∀ z ∈ orthant_sl (mA n), ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ z' ∈ orthant_sl (mA n), nrm (z' - z) < r →
        |phi2D b z' - phi2D b z| ≤ ((fun _ => (1 : ℝ)) z + δ) * nrm (z' - z) := by
    intro z _ δ hδ
    refine ⟨1, one_pos, fun z' _ _ => ?_⟩
    have h := eulip_phi2D hb z' z
    rw [one_mul] at h
    refine h.trans ?_
    change nrm (z' - z) ≤ (1 + δ) * nrm (z' - z)
    have := BstLean.Part153.nrm_nonneg (z' - z)
    nlinarith
  have hgrad : ∀ᵐ ξ ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun ξ => PhiS A₁ A₂ b (sphPt (c + τ • ξ))) ξ (Pi.single i 1)) ^ 2 ≤
        GamS A₁ A₂ c τ ξ := by
    have hfe : (fun ξ : Fin n → ℝ => PhiS A₁ A₂ b (sphPt (c + τ • ξ))) = fun ξ =>
        phi2D b (√(2 / (mA n : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) := by
      funext ξ
      rw [PhiS_sph hn1]
      exact BstLean.Part160.sig_eq_phi2D b _ _
    rw [hfe]
    filter_upwards [hne, BstLean.Part151.lemmaJ_shift A₁ A₂ c hτ.ne'] with ξ h1' h2'
    exact BstLean.Part153.gradSq_loc_le_sl hn1 A₁ A₂ c hτ (ℓ := fun _ => (1 : ℝ)) h2
      (fun _ _ => zero_le_one) ξ h1' h2'
  -- integrability
  have hinv := (BstLean.Part153.invMoment_le (p := 2 * q) (by omega) c hτ).1
  have hinvq := (BstLean.Part153.invMoment_le (p := q) (by omega) c hτ).1
  have hΓ : Integrable (fun ξ => √(GamS A₁ A₂ c τ ξ) ^ (2 * q)) (stdGauss (Fin n)) := by
    simp_rw [GamS_pow]
    have hm : Measurable (fun ξ : Fin n → ℝ => (2 / (mA n : ℝ)) ^ q *
        ((τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2) ^ q)) :=
      measurable_const.mul ((((measurable_const.mul (BstLean.Part153.cont_ns c τ).measurable.inv)).pow_const q).mul
        (((BstLean.Part153.measurable_opN_jacT_sj A₁ A₂ c τ).pow_const 2).pow_const q))
    refine Integrable.mono' (hinvq.const_mul ((2 / (mA n : ℝ)) ^ q * ((τ ^ 2) ^ q *
      ((opN A₂ * opN A₁) ^ 2) ^ q))) hm.aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
    have hj := BstLean.Part153.opN_jacT_le_sj A₁ A₂ (normSq_sphPt hn1 (c + τ • ξ))
    have hj2 : (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2) ^ q ≤ ((opN A₂ * opN A₁) ^ 2) ^ q :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (opN_nonneg _) hj 2) q
    have hN0 : 0 ≤ (normSq (c + τ • ξ))⁻¹ := inv_nonneg.2 (normSq_nonneg _)
    have hw0 : 0 ≤ (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q := pow_nonneg (mul_nonneg (sq_nonneg _) hN0) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (mul_nonneg hw0 (by positivity)))]
    have e : (2 / (mA n : ℝ)) ^ q * ((τ ^ 2) ^ q * ((opN A₂ * opN A₁) ^ 2) ^ q) *
        (normSq (c + τ • ξ))⁻¹ ^ q = (2 / (mA n : ℝ)) ^ q * ((τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q *
        ((opN A₂ * opN A₁) ^ 2) ^ q) := by rw [mul_pow]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hj2 hw0) (by positivity)
  have h := lemmaS_grad_p c hτ hK0 (PhiS_lip A₁ A₂ hb) (p := 2 * q) (by omega)
    (GamS_nonneg A₁ A₂ c τ) hΓ hgrad hinv hne
  simp only [PhiS_sph hn1] at h
  refine h.trans (le_of_eq ?_)
  congr 2
  simp_rw [GamS_pow]
  rw [integral_const_mul]
  rfl

/-- **The tail of `σ` from the moment of order `2q`**:
`Pr(|σ − Eσ| ≥ g) ≤ (π/2)^{2q}·E|g|^{2q}·t^q·X_q / g^{2q}`. -/
theorem sigD_tail {q : ℕ} (hq : 1 ≤ q) (hn : 4 * q + 1 < n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {b : Fin (mA n) → ℝ} (hb : 0 < normSq b) {g : ℝ} (hg : 0 < g) :
    (stdGauss (Fin n)).real
        {ξ | g ≤ |sigD A₁ A₂ c τ b ξ - ∫ ζ, sigD A₁ A₂ c τ b ζ ∂stdGauss (Fin n)|} ≤
      (π / 2) ^ (2 * q) * (gmom (2 * q) * ((2 / (mA n : ℝ)) ^ q * XqN q A₁ A₂ c τ)) /
        g ^ (2 * q) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hv := sigD_mom hq hn A₁ A₂ c hτ hb
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = ∫ ζ, sigD A₁ A₂ c τ b ζ ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hm₀] at hv ⊢
  obtain ⟨B, hB0, hB⟩ := BstLean.Part160.uD_bdd (by omega) (eulip_phi2D hb) A₁ A₂ c τ
  rw [← BstLean.Part160.sigD_eq] at hB
  have hm := BstLean.Part160.measurable_sigD hb A₁ A₂ c τ
  have hi : Integrable (fun ξ => |sigD A₁ A₂ c τ b ξ - m₀| ^ (2 * q)) (stdGauss (Fin n)) := by
    refine Integrable.of_bound ((hm.sub measurable_const).abs.pow_const _).aestronglyMeasurable
      ((B + |m₀|) ^ (2 * q)) (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    refine pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans ?_) _
    linarith [hB ξ]
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := stdGauss (Fin n))
    (Filter.Eventually.of_forall fun ξ =>
      (by positivity : 0 ≤ |sigD A₁ A₂ c τ b ξ - m₀| ^ (2 * q))) hi (g ^ (2 * q))
  have hsub : {ξ | g ≤ |sigD A₁ A₂ c τ b ξ - m₀|} ⊆
      {ξ | g ^ (2 * q) ≤ |sigD A₁ A₂ c τ b ξ - m₀| ^ (2 * q)} := fun ξ hξ =>
    pow_le_pow_left₀ hg.le hξ _
  have hmono := measureReal_mono (μ := stdGauss (Fin n)) hsub
  rw [le_div_iff₀ (pow_pos hg _), mul_comm]
  exact (mul_le_mul_of_nonneg_left hmono (pow_nonneg hg.le _)).trans (hM.trans hv)

end BstLean.Part165
