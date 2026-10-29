import BstLean.Part154Defs

/-!
# Part 154: Lemma MF, the facts (F1) to (F4)
Statements fixed by the lead agent; auxiliary lemmas (`normSq_eq_dot`, `MFHyp.coordL2`,
`MFHyp.dotL2`, `MFHyp.betaL2`, `MFHyp.gL2`, `MFHyp.sigL2`, …) are added above the headline statements.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (relu reluV normSq normSq_nonneg normSq_smul measurable_normSq)
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm)

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {f : Ω → Fin m → ℝ} {ℓ πg : ℝ}

/-- `δ_β² = E(β − 1)²`. -/
noncomputable def delta2 (μ : Measure Ω) (f : Ω → Fin m → ℝ) : ℝ := ∫ ω, (betaF μ f ω - 1) ^ 2 ∂μ


/-! ### Auxiliary algebra -/

lemma normSq_eq_dot (v : Fin m → ℝ) : normSq v = v ⬝ᵥ v := by
  simp only [normSq, dotProduct, sq]

lemma normSq_add' (a b : Fin m → ℝ) :
    normSq (a + b) = normSq a + 2 * (a ⬝ᵥ b) + normSq b := by
  simp only [normSq, dotProduct, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma sq_le_normSq (v : Fin m → ℝ) (i : Fin m) : v i ^ 2 ≤ normSq v :=
  Finset.single_le_sum (f := fun i => v i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

lemma betaF_eq (μ : Measure Ω) (f : Ω → Fin m → ℝ) (ω : Ω) :
    betaF μ f ω = (GamBarF μ f)⁻¹ * (fbar μ f ⬝ᵥ f ω) := by
  rw [betaF, dotProduct_comm, div_eq_inv_mul]

lemma gF_coord (μ : Measure Ω) (f : Ω → Fin m → ℝ) (ω : Ω) (i : Fin m) :
    gF μ f ω i = f ω i - fbar μ f i * betaF μ f ω := by
  simp only [gF, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma int_one_c (c : ℝ) : ∫ _ : Ω, c ∂μ = c := by simp

/-- If `C b = 0` and `bᵀ C = 0`, the quadratic form of `C` does not see a multiple of `b`. -/
lemma quad_shift (C : Fin m → Fin m → ℝ) (b h : Fin m → ℝ) (γ : ℝ)
    (h1 : ∀ i, ∑ j, C i j * b j = 0) (h2 : ∀ j, ∑ i, C i j * b i = 0) :
    ∑ i, ∑ j, C i j * ((h i - γ * b i) * (h j - γ * b j)) = ∑ i, ∑ j, C i j * (h i * h j) := by
  have t : ∀ i j, C i j * ((h i - γ * b i) * (h j - γ * b j)) =
      C i j * (h i * h j) - γ * (h i * (C i j * b j)) -
        γ * ((h j - γ * b j) * (C i j * b i)) := by intros; ring
  have a : ∑ i, ∑ j, γ * (h i * (C i j * b j)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, h1, mul_zero, mul_zero]
  have b' : ∑ i, ∑ j, γ * ((h j - γ * b j) * (C i j * b i)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, h2, mul_zero, mul_zero]
  simp only [t, Finset.sum_sub_distrib]
  rw [a, b', sub_zero, sub_zero]

lemma quad_int (C : Fin m → Fin m → ℝ) (x : Ω → Fin m → ℝ)
    (hx : ∀ i j, Integrable (fun ω => x ω i * x ω j) μ) :
    ∫ ω, ∑ i, ∑ j, C i j * (x ω i * x ω j) ∂μ = ∑ i, ∑ j, C i j * ∫ ω, x ω i * x ω j ∂μ := by
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hx i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hx i j).const_mul _]
  simp only [integral_const_mul]

/-! ### Integrability -/

theorem MFHyp.int_sq (H : MFHyp μ f ℓ πg) : Integrable (fun ω => normSq (f ω)) μ := by
  have hm : Measurable (fun ω => normSq (f ω)) := measurable_normSq.comp H.hf
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 H.h4).integrable one_le_two

lemma MFHyp.coordL2 (H : MFHyp μ f ℓ πg) (i : Fin m) : MemLp (fun ω => f ω i) 2 μ := by
  have hm : Measurable (fun ω => f ω i) := (measurable_pi_apply i).comp H.hf
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 ?_
  refine Integrable.mono' H.int_sq (hm.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_normSq _ i

lemma MFHyp.dotL2 (H : MFHyp μ f ℓ πg) (w : Fin m → ℝ) : MemLp (fun ω => w ⬝ᵥ f ω) 2 μ := by
  simp only [dotProduct]
  exact memLp_finsetSum _ fun i _ => (H.coordL2 i).const_mul (w i)

theorem MFHyp.int_coord (H : MFHyp μ f ℓ πg) (i : Fin m) : Integrable (fun ω => f ω i) μ :=
  (H.coordL2 i).integrable one_le_two

theorem MFHyp.int_dot (H : MFHyp μ f ℓ πg) (w : Fin m → ℝ) :
    Integrable (fun ω => w ⬝ᵥ f ω) μ ∧ ∫ ω, w ⬝ᵥ f ω ∂μ = w ⬝ᵥ fbar μ f := by
  refine ⟨(H.dotL2 w).integrable one_le_two, ?_⟩
  simp only [dotProduct]
  rw [integral_finsetSum _ fun i _ => (H.int_coord i).const_mul (w i)]
  simp only [integral_const_mul, fbar]

lemma MFHyp.meas_dot (H : MFHyp μ f ℓ πg) (w : Fin m → ℝ) : Measurable (fun ω => w ⬝ᵥ f ω) :=
  ((continuous_const (y := w)).dotProduct continuous_id).measurable.comp H.hf

theorem MFHyp.meas_beta (H : MFHyp μ f ℓ πg) : Measurable (betaF μ f) := by
  rw [show betaF μ f = fun ω => (GamBarF μ f)⁻¹ * (fbar μ f ⬝ᵥ f ω) from funext (betaF_eq μ f)]
  exact (H.meas_dot _).const_mul _

lemma MFHyp.betaL2 (H : MFHyp μ f ℓ πg) : MemLp (betaF μ f) 2 μ := by
  rw [show betaF μ f = fun ω => (GamBarF μ f)⁻¹ * (fbar μ f ⬝ᵥ f ω) from funext (betaF_eq μ f)]
  exact (H.dotL2 _).const_mul _

lemma MFHyp.gL2 (H : MFHyp μ f ℓ πg) (i : Fin m) : MemLp (fun ω => gF μ f ω i) 2 μ := by
  rw [show (fun ω => gF μ f ω i) = fun ω => f ω i - fbar μ f i * betaF μ f ω from
    funext fun ω => gF_coord μ f ω i]
  exact (H.coordL2 i).sub (H.betaL2.const_mul _)

theorem MFHyp.meas_g (H : MFHyp μ f ℓ πg) : Measurable (gF μ f) := by
  refine measurable_pi_iff.2 fun i => ?_
  rw [show (fun ω => gF μ f ω i) = fun ω => f ω i - fbar μ f i * betaF μ f ω from
    funext fun ω => gF_coord μ f ω i]
  exact ((measurable_pi_apply i).comp H.hf).sub (H.meas_beta.const_mul _)

theorem MFHyp.meas_sig (H : MFHyp μ f ℓ πg) : Measurable (sig2F μ f) :=
  measurable_normSq.comp H.meas_g

theorem sig2F_nonneg (μ : Measure Ω) (f : Ω → Fin m → ℝ) (ω : Ω) : 0 ≤ sig2F μ f ω :=
  normSq_nonneg _

/-- `⟨z, f⟩ = β·⟨z, f̄⟩ + ⟨z, Π f⟩` (the regression). -/
theorem dot_decomp (μ : Measure Ω) (f : Ω → Fin m → ℝ) (z : Fin m → ℝ) (ω : Ω) :
    z ⬝ᵥ f ω = betaF μ f ω * (z ⬝ᵥ fbar μ f) + z ⬝ᵥ gF μ f ω := by
  simp only [gF, dotProduct_sub, dotProduct_smul, smul_eq_mul]; ring

theorem MFHyp.g_dot_fbar (H : MFHyp μ f ℓ πg) (ω : Ω) : gF μ f ω ⬝ᵥ fbar μ f = 0 := by
  have hG : GamBarF μ f ≠ 0 := H.hbar.ne'
  have h1 : fbar μ f ⬝ᵥ fbar μ f = GamBarF μ f := (normSq_eq_dot _).symm
  have h2 : betaF μ f ω * GamBarF μ f = f ω ⬝ᵥ fbar μ f := by rw [betaF, div_mul_cancel₀ _ hG]
  rw [gF, sub_dotProduct, smul_dotProduct, smul_eq_mul, h1, h2, sub_self]

/-- `|f|² = β²Γ̄ + ς²`. -/
theorem MFHyp.normSq_split (H : MFHyp μ f ℓ πg) (ω : Ω) :
    normSq (f ω) = betaF μ f ω ^ 2 * GamBarF μ f + sig2F μ f ω := by
  have e : f ω = gF μ f ω + betaF μ f ω • fbar μ f := by simp [gF]
  have h := normSq_add' (gF μ f ω) (betaF μ f ω • fbar μ f)
  rw [← e, dotProduct_smul, H.g_dot_fbar, normSq_smul, smul_zero, mul_zero, add_zero] at h
  rw [h, sig2F, GamBarF]; ring

lemma MFHyp.sig_le (H : MFHyp μ f ℓ πg) (ω : Ω) : sig2F μ f ω ≤ normSq (f ω) := by
  rw [H.normSq_split ω]
  have := mul_nonneg (sq_nonneg (betaF μ f ω)) H.hbar.le
  linarith

lemma MFHyp.sigL2 (H : MFHyp μ f ℓ πg) : MemLp (sig2F μ f) 2 μ := by
  refine (memLp_two_iff_integrable_sq H.meas_sig.aestronglyMeasurable).2 ?_
  refine Integrable.mono' H.h4 (H.meas_sig.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (sig2F_nonneg μ f ω) (H.sig_le ω) 2

lemma MFHyp.sF_pos_aux (H : MFHyp μ f ℓ πg) : 0 < sF μ f ∧ sF μ f ^ 2 = sF2 μ f :=
  ⟨Real.sqrt_pos.2 H.hs, Real.sq_sqrt H.hs.le⟩

/-- (F1): `E β = 1`, and `Γ̄·E(β − 1)² ≤ ℓ²`. -/
theorem MFHyp.F1 (H : MFHyp μ f ℓ πg) :
    Integrable (betaF μ f) μ ∧ ∫ ω, betaF μ f ω ∂μ = 1 ∧
    Integrable (fun ω => (betaF μ f ω - 1) ^ 2) μ ∧ 0 ≤ delta2 μ f ∧
    GamBarF μ f * delta2 μ f ≤ ℓ ^ 2 := by
  have hG := H.hbar
  have hG' : GamBarF μ f ≠ 0 := hG.ne'
  have hbb : fbar μ f ⬝ᵥ fbar μ f = GamBarF μ f := (normSq_eq_dot _).symm
  have hβ : Integrable (betaF μ f) μ := H.betaL2.integrable one_le_two
  have hβ1 : ∫ ω, betaF μ f ω ∂μ = 1 := by
    simp only [betaF_eq]
    rw [integral_const_mul, (H.int_dot _).2, hbb]
    exact inv_mul_cancel₀ hG'
  have key : ∀ ω, (betaF μ f ω - 1) ^ 2 =
      (GamBarF μ f ^ 2)⁻¹ * (fbar μ f ⬝ᵥ f ω - fbar μ f ⬝ᵥ fbar μ f) ^ 2 := by
    intro ω
    have : betaF μ f ω - 1 = (GamBarF μ f)⁻¹ * (fbar μ f ⬝ᵥ f ω - fbar μ f ⬝ᵥ fbar μ f) := by
      rw [betaF_eq, hbb, mul_sub, inv_mul_cancel₀ hG']
    rw [this, mul_pow, inv_pow]
  have hi : Integrable (fun ω => (betaF μ f ω - 1) ^ 2) μ :=
    (H.betaL2.sub (memLp_const 1)).integrable_sq
  have h0 : 0 ≤ delta2 μ f := integral_nonneg fun ω => sq_nonneg _
  refine ⟨hβ, hβ1, hi, h0, ?_⟩
  have hM : ∫ ω, (fbar μ f ⬝ᵥ f ω - fbar μ f ⬝ᵥ fbar μ f) ^ 2 ∂μ ≤ ℓ ^ 2 * GamBarF μ f :=
    H.M1 (fbar μ f)
  rw [delta2]
  simp only [key]
  rw [integral_const_mul]
  have e : ∀ I : ℝ, GamBarF μ f * ((GamBarF μ f ^ 2)⁻¹ * I) = (GamBarF μ f)⁻¹ * I := by
    intro I
    rw [← mul_assoc, sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hG', one_mul]
  rw [e]
  calc (GamBarF μ f)⁻¹ * _ ≤ (GamBarF μ f)⁻¹ * (ℓ ^ 2 * GamBarF μ f) :=
        mul_le_mul_of_nonneg_left hM (inv_nonneg.2 hG.le)
    _ = ℓ ^ 2 := by rw [mul_comm (ℓ ^ 2), ← mul_assoc, inv_mul_cancel₀ hG', one_mul]

/-- (F2): `E ς² = s² − Γ̄·δ_β²`. -/
theorem MFHyp.F2 (H : MFHyp μ f ℓ πg) :
    Integrable (sig2F μ f) μ ∧ ∫ ω, sig2F μ f ω ∂μ = sF2 μ f - GamBarF μ f * delta2 μ f := by
  obtain ⟨hβ, hβ1, hi, _, _⟩ := H.F1
  have hβ2 : Integrable (fun ω => betaF μ f ω ^ 2) μ := H.betaL2.integrable_sq
  have e : ∀ ω, sig2F μ f ω = normSq (f ω) - GamBarF μ f * betaF μ f ω ^ 2 := by
    intro ω; rw [H.normSq_split ω]; ring
  have e2 : ∀ ω, betaF μ f ω ^ 2 = (betaF μ f ω - 1) ^ 2 + 2 * betaF μ f ω - 1 := by
    intro ω; ring
  have hint : Integrable (sig2F μ f) μ := H.sigL2.integrable one_le_two
  refine ⟨hint, ?_⟩
  have hβ2v : ∫ ω, betaF μ f ω ^ 2 ∂μ = delta2 μ f + 1 := by
    have h1 : ∫ ω, ((betaF μ f ω - 1) ^ 2 + 2 * betaF μ f ω - 1) ∂μ = delta2 μ f + 1 := by
      rw [integral_sub (show Integrable (fun ω => (betaF μ f ω - 1) ^ 2 + 2 * betaF μ f ω) μ from
          hi.add (hβ.const_mul 2)) (integrable_const 1),
        integral_add hi (hβ.const_mul 2), integral_const_mul, hβ1, int_one_c, delta2]
      ring
    rw [← h1]
    exact integral_congr_ae (ae_of_all _ e2)
  have h2 : ∫ ω, (normSq (f ω) - GamBarF μ f * betaF μ f ω ^ 2) ∂μ =
      sF2 μ f - GamBarF μ f * delta2 μ f := by
    rw [integral_sub H.int_sq (hβ2.const_mul _), integral_const_mul, hβ2v, sF2, GamF]; ring
  rw [← h2]
  exact integral_congr_ae (ae_of_all _ e)

/-- (F3): `E(ς² − s²)² ≤ ν·s⁴`, `ν = 4ϱ + ϱ²`, `ϱ = ℓ²/s²`. -/
theorem MFHyp.F3 (H : MFHyp μ f ℓ πg) :
    Integrable (fun ω => (sig2F μ f ω - sF2 μ f) ^ 2) μ ∧
    ∫ ω, (sig2F μ f ω - sF2 μ f) ^ 2 ∂μ ≤ nuR (ℓ ^ 2 / sF2 μ f) * sF2 μ f ^ 2 := by
  obtain ⟨hsi, hsv⟩ := H.F2
  obtain ⟨_, _, _, hd0, hd1⟩ := H.F1
  have hs := H.hs
  have hM2 := H.M2
  have hc : ∀ c : ℝ, Integrable (fun ω => (sig2F μ f ω - c) ^ 2) μ := fun c =>
    (H.sigL2.sub (memLp_const c)).integrable_sq
  refine ⟨hc _, ?_⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, ∫ ω, sig2F μ f ω ∂μ = E := ⟨_, rfl⟩
  rw [hE] at hM2 hsv
  have e : ∀ ω, (sig2F μ f ω - sF2 μ f) ^ 2 =
      (sig2F μ f ω - E) ^ 2 + (2 * (E - sF2 μ f)) * sig2F μ f ω + (sF2 μ f ^ 2 - E ^ 2) := by
    intro ω; ring
  have hint : ∫ ω, (sig2F μ f ω - sF2 μ f) ^ 2 ∂μ =
      ∫ ω, (sig2F μ f ω - E) ^ 2 ∂μ + (E - sF2 μ f) ^ 2 := by
    have h1 : ∫ ω, ((sig2F μ f ω - E) ^ 2 + (2 * (E - sF2 μ f)) * sig2F μ f ω +
        (sF2 μ f ^ 2 - E ^ 2)) ∂μ = ∫ ω, (sig2F μ f ω - E) ^ 2 ∂μ + (E - sF2 μ f) ^ 2 := by
      rw [integral_add (show Integrable (fun ω => (sig2F μ f ω - E) ^ 2 +
          (2 * (E - sF2 μ f)) * sig2F μ f ω) μ from (hc E).add (hsi.const_mul _))
          (integrable_const _),
        integral_add (hc E) (hsi.const_mul _), integral_const_mul, int_one_c, hE]
      ring
    rw [← h1]
    exact integral_congr_ae (ae_of_all _ e)
  rw [hint]
  have hGd0 : 0 ≤ GamBarF μ f * delta2 μ f := mul_nonneg H.hbar.le hd0
  have ha : (GamBarF μ f * delta2 μ f) ^ 2 ≤ (ℓ ^ 2) ^ 2 := pow_le_pow_left₀ hGd0 hd1 2
  have hb : 0 ≤ ℓ ^ 2 * (GamBarF μ f * delta2 μ f) := mul_nonneg (sq_nonneg _) hGd0
  have hE2 : (E - sF2 μ f) ^ 2 = (GamBarF μ f * delta2 μ f) ^ 2 := by rw [hsv]; ring
  have hnu : nuR (ℓ ^ 2 / sF2 μ f) * sF2 μ f ^ 2 = 4 * ℓ ^ 2 * sF2 μ f + (ℓ ^ 2) ^ 2 := by
    rw [nuR, div_pow, add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hs.ne'), mul_assoc,
      sq (sF2 μ f), ← mul_assoc (ℓ ^ 2 / sF2 μ f), div_mul_cancel₀ _ hs.ne']
    ring
  rw [hnu, hE2]
  have hM2' : ∫ ω, (sig2F μ f ω - E) ^ 2 ∂μ ≤ 4 * ℓ ^ 2 * (sF2 μ f - GamBarF μ f * delta2 μ f) := by
    rw [← hsv]; exact hM2
  linarith

/-- (F4), first part: the mean of `Π f` is `0`. -/
theorem MFHyp.F4a (H : MFHyp μ f ℓ πg) (i : Fin m) :
    Integrable (fun ω => gF μ f ω i) μ ∧ ∫ ω, gF μ f ω i ∂μ = 0 := by
  obtain ⟨hβ, hβ1, _⟩ := H.F1
  rw [show (fun ω => gF μ f ω i) = fun ω => f ω i - fbar μ f i * betaF μ f ω from
    funext fun ω => gF_coord μ f ω i]
  refine ⟨(H.int_coord i).sub (hβ.const_mul _), ?_⟩
  rw [integral_sub (H.int_coord i) (hβ.const_mul _), integral_const_mul, hβ1, mul_one]
  exact sub_self _

/-- (F4), second part: `|E[φ·Π f]|² ≤ ℓ²·E φ²`. -/
theorem MFHyp.F4b (H : MFHyp μ f ℓ πg) {φ : Ω → ℝ} (hφ : Measurable φ)
    (hφ2 : Integrable (fun ω => φ ω ^ 2) μ) :
    (∀ i, Integrable (fun ω => φ ω * gF μ f ω i) μ) ∧
    ∑ i, (∫ ω, φ ω * gF μ f ω i ∂μ) ^ 2 ≤ ℓ ^ 2 * ∫ ω, φ ω ^ 2 ∂μ := by
  have hG' : GamBarF μ f ≠ 0 := H.hbar.ne'
  have hbb : fbar μ f ⬝ᵥ fbar μ f = GamBarF μ f := (normSq_eq_dot _).symm
  have hφL2 : MemLp φ 2 μ := (memLp_two_iff_integrable_sq hφ.aestronglyMeasurable).2 hφ2
  have hgi : ∀ i, Integrable (fun ω => φ ω * gF μ f ω i) μ := fun i =>
    hφL2.integrable_mul (H.gL2 i)
  refine ⟨hgi, ?_⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin m → ℝ, ∀ i, ∫ ω, φ ω * gF μ f ω i ∂μ = v i := ⟨_, fun _ => rfl⟩
  simp only [hv]
  have hψL2 : MemLp (fun ω => v ⬝ᵥ gF μ f ω) 2 μ := by
    simp only [dotProduct]
    exact memLp_finsetSum _ fun i _ => (H.gL2 i).const_mul (v i)
  have hφψi : Integrable (fun ω => φ ω * (v ⬝ᵥ gF μ f ω)) μ := hφL2.integrable_mul hψL2
  have hψsq : Integrable (fun ω => (v ⬝ᵥ gF μ f ω) ^ 2) μ := hψL2.integrable_sq
  have hφψ : ∫ ω, φ ω * (v ⬝ᵥ gF μ f ω) ∂μ = normSq v := by
    have e : ∀ ω, φ ω * (v ⬝ᵥ gF μ f ω) = ∑ i, v i * (φ ω * gF μ f ω i) := by
      intro ω
      simp only [dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [integral_congr_ae (ae_of_all _ e),
      integral_finsetSum _ fun i _ => (hgi i).const_mul _]
    simp only [integral_const_mul, hv, normSq]
    exact Finset.sum_congr rfl fun i _ => (sq (v i)).symm
  -- the projection of `v`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (v ⬝ᵥ fbar μ f) / GamBarF μ f := ⟨_, rfl⟩
  obtain ⟨Pv, hPv⟩ : ∃ P : Fin m → ℝ, P = v - c • fbar μ f := ⟨_, rfl⟩
  have hP0 : Pv ⬝ᵥ fbar μ f = 0 := by
    rw [hPv, sub_dotProduct, smul_dotProduct, smul_eq_mul, hbb, hc, div_mul_cancel₀ _ hG',
      sub_self]
  have e : ∀ ω, v ⬝ᵥ gF μ f ω = Pv ⬝ᵥ f ω - Pv ⬝ᵥ fbar μ f := by
    intro ω
    rw [hP0, sub_zero, hPv, gF, dotProduct_sub, dotProduct_smul, sub_dotProduct, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, betaF, hc, dotProduct_comm (fbar μ f) (f ω)]
    ring
  have hnP : normSq Pv ≤ normSq v := by
    have hv' : v = Pv + c • fbar μ f := by rw [hPv, sub_add_cancel]
    have h := normSq_add' Pv (c • fbar μ f)
    rw [← hv', dotProduct_smul, hP0, normSq_smul, smul_zero, mul_zero, add_zero] at h
    have := mul_nonneg (sq_nonneg c) (normSq_nonneg (fbar μ f))
    linarith
  have hψ2 : ∫ ω, (v ⬝ᵥ gF μ f ω) ^ 2 ∂μ ≤ ℓ ^ 2 * normSq v := by
    calc ∫ ω, (v ⬝ᵥ gF μ f ω) ^ 2 ∂μ = ∫ ω, (Pv ⬝ᵥ f ω - Pv ⬝ᵥ fbar μ f) ^ 2 ∂μ :=
          integral_congr_ae (ae_of_all _ fun ω => by simp only [e ω])
      _ ≤ ℓ ^ 2 * normSq Pv := H.M1 Pv
      _ ≤ ℓ ^ 2 * normSq v := mul_le_mul_of_nonneg_left hnP (sq_nonneg _)
  have ex : ∀ ω, (ℓ ^ 2 * φ ω - v ⬝ᵥ gF μ f ω) ^ 2 =
      (ℓ ^ 2) ^ 2 * φ ω ^ 2 - 2 * ℓ ^ 2 * (φ ω * (v ⬝ᵥ gF μ f ω)) + (v ⬝ᵥ gF μ f ω) ^ 2 := by
    intro ω; ring
  have h0 : 0 ≤ ∫ ω, (ℓ ^ 2 * φ ω - v ⬝ᵥ gF μ f ω) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  rw [integral_congr_ae (ae_of_all _ ex),
    integral_add (show Integrable (fun ω => (ℓ ^ 2) ^ 2 * φ ω ^ 2 -
      2 * ℓ ^ 2 * (φ ω * (v ⬝ᵥ gF μ f ω))) μ from
      (hφ2.const_mul _).sub (hφψi.const_mul _)) hψsq,
    integral_sub (hφ2.const_mul _) (hφψi.const_mul _), integral_const_mul, integral_const_mul,
    hφψ] at h0
  have hℓ2 : 0 < ℓ ^ 2 := pow_pos H.hℓ 2
  have hfin : ℓ ^ 2 * normSq v ≤ ℓ ^ 2 * (ℓ ^ 2 * ∫ ω, φ ω ^ 2 ∂μ) := by linarith
  exact le_of_mul_le_mul_left hfin hℓ2

/-- (F4), third part: `E_{ω,ω′} 𝖼(ω, ω′)² ≤ ‖H_f‖²_HS`. -/
theorem MFHyp.F4c (H : MFHyp μ f ℓ πg) :
    Integrable (fun p : Ω × Ω => (gF μ f p.1 ⬝ᵥ gF μ f p.2) ^ 2) (μ.prod μ) ∧
    ∫ p : Ω × Ω, (gF μ f p.1 ⬝ᵥ gF μ f p.2) ^ 2 ∂(μ.prod μ) ≤ hsF μ f := by
  have hgg : ∀ i j, Integrable (fun ω => gF μ f ω i * gF μ f ω j) μ := fun i j =>
    (H.gL2 i).integrable_mul (H.gL2 j)
  have hhh : ∀ i j, Integrable (fun ω => (f ω i - fbar μ f i) * (f ω j - fbar μ f j)) μ :=
    fun i j => ((H.coordL2 i).sub (memLp_const _)).integrable_mul
      ((H.coordL2 j).sub (memLp_const _))
  obtain ⟨C, hC⟩ : ∃ C : Fin m → Fin m → ℝ, ∀ i j, ∫ ω, gF μ f ω i * gF μ f ω j ∂μ = C i j :=
    ⟨_, fun _ _ => rfl⟩
  have ex : ∀ p : Ω × Ω, (gF μ f p.1 ⬝ᵥ gF μ f p.2) ^ 2 =
      ∑ i, ∑ j, (gF μ f p.1 i * gF μ f p.1 j) * (gF μ f p.2 i * gF μ f p.2 j) := by
    intro p
    rw [sq, dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hterm : ∀ i j, Integrable (fun p : Ω × Ω =>
      (gF μ f p.1 i * gF μ f p.1 j) * (gF μ f p.2 i * gF μ f p.2 j)) (μ.prod μ) :=
    fun i j => (hgg i j).mul_prod (hgg i j)
  have hsum : Integrable (fun p : Ω × Ω =>
      ∑ i, ∑ j, (gF μ f p.1 i * gF μ f p.1 j) * (gF μ f p.2 i * gF μ f p.2 j)) (μ.prod μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm i j
  have hI : ∫ p : Ω × Ω, (gF μ f p.1 ⬝ᵥ gF μ f p.2) ^ 2 ∂(μ.prod μ) = ∑ i, ∑ j, C i j ^ 2 := by
    rw [integral_congr_ae (ae_of_all _ ex),
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hterm i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_prod_mul (fun ω => gF μ f ω i * gF μ f ω j) (fun ω => gF μ f ω i * gF μ f ω j),
      hC, sq]
  refine ⟨(integrable_congr (ae_of_all _ ex)).2 hsum, ?_⟩
  rw [hI]
  have hCs : ∀ i j, C i j = C j i := by
    intro i j
    rw [← hC i j, ← hC j i]
    exact integral_congr_ae (ae_of_all _ fun ω => mul_comm _ _)
  have hCfb : ∀ i, ∑ j, C i j * fbar μ f j = 0 := by
    intro i
    have z : ∀ ω, ∑ j, gF μ f ω i * gF μ f ω j * fbar μ f j = 0 := by
      intro ω
      have h := H.g_dot_fbar ω
      simp only [dotProduct] at h
      simp only [mul_assoc]
      rw [← Finset.mul_sum, h, mul_zero]
    calc ∑ j, C i j * fbar μ f j
        = ∑ j, ∫ ω, gF μ f ω i * gF μ f ω j * fbar μ f j ∂μ := by
          simp only [← hC, integral_mul_const]
      _ = ∫ ω, ∑ j, gF μ f ω i * gF μ f ω j * fbar μ f j ∂μ :=
          (integral_finsetSum _ fun j _ => (hgg i j).mul_const _).symm
      _ = 0 := by simp only [z, integral_zero]
  have hCfb2 : ∀ j, ∑ i, C i j * fbar μ f i = 0 := fun j =>
    (Finset.sum_congr rfl fun i _ => by rw [hCs i j]).trans (hCfb j)
  have key : ∑ i, ∑ j, C i j ^ 2 = ∑ i, ∑ j, C i j * covF μ f i j := by
    have q1 := quad_int (μ := μ) C (gF μ f) hgg
    have q2 := quad_int (μ := μ) C (fun ω i => f ω i - fbar μ f i) hhh
    have pt : ∀ ω, ∑ i, ∑ j, C i j * (gF μ f ω i * gF μ f ω j) =
        ∑ i, ∑ j, C i j * ((f ω i - fbar μ f i) * (f ω j - fbar μ f j)) := by
      intro ω
      have eg : ∀ i, gF μ f ω i = (f ω i - fbar μ f i) - (betaF μ f ω - 1) * fbar μ f i := by
        intro i; rw [gF_coord]; ring
      simp only [eg]
      exact quad_shift C (fbar μ f) (fun i => f ω i - fbar μ f i) (betaF μ f ω - 1) hCfb hCfb2
    calc ∑ i, ∑ j, C i j ^ 2 = ∑ i, ∑ j, C i j * ∫ ω, gF μ f ω i * gF μ f ω j ∂μ := by
          simp only [hC, sq]
      _ = ∫ ω, ∑ i, ∑ j, C i j * (gF μ f ω i * gF μ f ω j) ∂μ := q1.symm
      _ = ∫ ω, ∑ i, ∑ j, C i j * ((f ω i - fbar μ f i) * (f ω j - fbar μ f j)) ∂μ :=
          integral_congr_ae (ae_of_all _ pt)
      _ = ∑ i, ∑ j, C i j * covF μ f i j := q2
  have nn : 0 ≤ ∑ i, ∑ j, (C i j - covF μ f i j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hexp : ∑ i, ∑ j, (C i j - covF μ f i j) ^ 2 =
      ∑ i, ∑ j, C i j ^ 2 - 2 * ∑ i, ∑ j, C i j * covF μ f i j +
        ∑ i, ∑ j, covF μ f i j ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  rw [hsF]
  linarith

/-- `E ς ≤ s` and `E[ς; ς² < s²/2] ≤ (s/√2)·π_g`. -/
theorem MFHyp.sig_int (H : MFHyp μ f ℓ πg) :
    Integrable (fun ω => √(sig2F μ f ω)) μ ∧ ∫ ω, √(sig2F μ f ω) ∂μ ≤ sF μ f ∧
    ∫ ω in {ω | sig2F μ f ω < sF2 μ f / 2}, √(sig2F μ f ω) ∂μ ≤ sF μ f / √2 * πg := by
  obtain ⟨hsi, hsv⟩ := H.F2
  obtain ⟨_, _, _, hd0, _⟩ := H.F1
  obtain ⟨hs0, hs2⟩ := H.sF_pos_aux
  have hm : Measurable (fun ω => √(sig2F μ f ω)) := H.meas_sig.sqrt
  have hsq : ∀ ω, √(sig2F μ f ω) ^ 2 = sig2F μ f ω := fun ω =>
    Real.sq_sqrt (sig2F_nonneg μ f ω)
  have hL2 : MemLp (fun ω => √(sig2F μ f ω)) 2 μ :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
      ((integrable_congr (ae_of_all _ hsq)).2 hsi)
  have hi : Integrable (fun ω => √(sig2F μ f ω)) μ := hL2.integrable one_le_two
  refine ⟨hi, ?_, ?_⟩
  · have h0 : 0 ≤ ∫ ω, (√(sig2F μ f ω) - sF μ f) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    have ex : ∀ ω, (√(sig2F μ f ω) - sF μ f) ^ 2 =
        sig2F μ f ω - 2 * sF μ f * √(sig2F μ f ω) + sF μ f ^ 2 := by
      intro ω; rw [sub_sq, hsq]; ring
    rw [integral_congr_ae (ae_of_all _ ex),
      integral_add (show Integrable (fun ω => sig2F μ f ω - 2 * sF μ f * √(sig2F μ f ω)) μ from
        hsi.sub (hi.const_mul _)) (integrable_const _),
      integral_sub hsi (hi.const_mul _), integral_const_mul, int_one_c, hsv] at h0
    have hGd0 : 0 ≤ GamBarF μ f * delta2 μ f := mul_nonneg H.hbar.le hd0
    have hfin : sF μ f * ∫ ω, √(sig2F μ f ω) ∂μ ≤ sF μ f * sF μ f := by
      have : sF μ f * sF μ f = sF2 μ f := by rw [← sq, hs2]
      linarith
    exact le_of_mul_le_mul_left hfin hs0
  · have hA : MeasurableSet {ω | sig2F μ f ω < sF2 μ f / 2} :=
      measurableSet_lt H.meas_sig measurable_const
    have hb : ∀ ω ∈ {ω | sig2F μ f ω < sF2 μ f / 2}, √(sig2F μ f ω) ≤ sF μ f / √2 := by
      intro ω hω
      rw [sF, ← Real.sqrt_div H.hs.le]
      exact Real.sqrt_le_sqrt (le_of_lt hω)
    calc ∫ ω in {ω | sig2F μ f ω < sF2 μ f / 2}, √(sig2F μ f ω) ∂μ
        ≤ ∫ ω in {ω | sig2F μ f ω < sF2 μ f / 2}, sF μ f / √2 ∂μ :=
          setIntegral_mono_on hi.integrableOn (integrable_const _).integrableOn hA hb
      _ = μ.real {ω | sig2F μ f ω < sF2 μ f / 2} * (sF μ f / √2) := by
          rw [setIntegral_const, smul_eq_mul]
      _ ≤ πg * (sF μ f / √2) :=
          mul_le_mul_of_nonneg_right H.M3 (div_nonneg hs0.le (Real.sqrt_nonneg _))
      _ = sF μ f / √2 * πg := mul_comm _ _

theorem MFHyp.sF_pos (H : MFHyp μ f ℓ πg) : 0 < sF μ f ∧ sF μ f ^ 2 = sF2 μ f :=
  H.sF_pos_aux

end BstLean.Part154
