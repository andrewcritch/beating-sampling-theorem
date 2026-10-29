import BstLean.Part254SharpData

/-! Actual quadratic-form bounds on the exact Option B event. The fourth-moment
bound remains a separate premise, as it does in Part238 and Part253. -/
namespace BstLean.Part254
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part208 BstLean.Part238 BstLean.Part251 BstLean.Part249
open BstLean.Part199 (exampleWide exampleCore example_nested)
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nrm Xi4)

theorem Dq_optionB_gaussian {n : ℕ} (hn : 11883 ≤ n) (D : Design n) (k : Ret n)
    (hτ : 0 < D.tau0 k)
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Icc (46 / 100) (528 / 1000))
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤ (13 / 10) * (2 / (n : ℝ)) / n)
    (hC : k ∈ agentEv D (optionBSharp n)) (v : Fin (mA n) → ℝ) :
    Dq k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) v ≤
      fixedGaussianCovariance n (thetaC k.1.2 (D.tau0 k)) * (2 / (n : ℝ)) / n * normSq v := by
  set θ := thetaC k.1.2 (D.tau0 k) with hθd
  have hθ1 : θ < 1 := hw.2.trans_lt (by norm_num)
  have hc : k.1.2 ≠ 0 := ne_zero_of_thetaC_lt (by omega) hτ hθ1
  obtain ⟨hR, hat, hchi⟩ := chi_core_M12 hn k.1.2 hτ hw.1 hw.2
  obtain ⟨hr₀, -⟩ := BstLean.Part235.wide_radius_caps hn hw.1 hw.2
  obtain ⟨hr₁, -⟩ := BstLean.Part235.core_radius_caps hn hw.1 hw.2
  obtain ⟨hcau, ha, hu⟩ := centre_decomp hc
  have hθ0 : 0 ≤ θ := by linarith [hw.1]
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hE : 0 ≤ (1 - 4 * θ / n)⁻¹ := by
    apply inv_nonneg.mpr
    have : 4 * θ / (n : ℝ) ≤ 1 :=
      (div_le_one (by linarith)).mpr (by linarith [hw.2])
    linarith
  have hsm1 := axialProjLower_le_one n ha hτ exampleCore.t_nonneg exampleCore.z_nonneg hat
  have hχ0 : 0 ≤ chiCore n (nrm k.1.2) (D.tau0 k) exampleCore.t exampleCore.z
      (axialProjLower n (nrm k.1.2) (D.tau0 k) exampleCore.t exampleCore.z) (63 / 100) := by
    unfold chiCore
    exact chi_nonneg hR (by norm_num) hsm1
  have hK : min (sharpK (595 / 1000) (35 / 1000) (25 / 100)
      (chiCore n (nrm k.1.2) (D.tau0 k) exampleCore.t exampleCore.z
        (axialProjLower n (nrm k.1.2) (D.tau0 k) exampleCore.t exampleCore.z) (63 / 100)))
      (ta_lam (595 / 1000) (35 / 1000) (25 / 100)) ≤ fixedCore :=
    min_le_min_right _ (sharpK_mono (by norm_num) (by norm_num) hχ0 hchi)
  have hb : sharpBadMass n exampleWide exampleCore (67 / 100)
      (595 / 1000) (35 / 1000) (25 / 100) (63 / 100)
      ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ≤ optionBDelta n / (1 / 4000) := by
    rcases hC hτ with hno | hb
    · exact False.elim (hno hw)
    · exact hb
  have hd := Dq_gaussian_joint (by omega : 6 ≤ n) k.2.1.1.1 k.2.1.1.2
    k.1.2 (uC k.1.2) hcau ha hu hτ exampleWide exampleCore example_nested
    (by norm_num : (0 : ℝ) ≤ 595 / 1000) (by norm_num : (0 : ℝ) ≤ 35 / 1000)
    (by norm_num : (0 : ℝ) ≤ 25 / 100) (by norm_num : (0 : ℝ) ≤ 67 / 100)
    (by norm_num : (0 : ℝ) ≤ 13 / 10) hθ1 (by linarith) (by linarith) hR
    (by norm_num) hsm1 (centre_proj_lower' hcau hu ha hτ hat) hb hX v
  refine hd.trans ?_
  apply mul_le_mul_of_nonneg_right _ (normSq_nonneg v)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ 2 / (n : ℝ))
  exact gaussianScalar_mono_K hθ0 hE hK

theorem localScalar (i : Fin 60) {θ : ℝ} (hθ : θ ∈ cell i) :
    fixedGaussianCovariance 12225 θ ≤ capTable i := by
  have hi := cell_needed hθ
  have hu : cellUpper i ≤ (528 / 1000 : ℝ) :=
    (min_le_right _ _).trans (by norm_num [worldUpper])
  have hθ0 : 0 ≤ θ := by linarith [(cell_window hθ).1]
  exact (fixedGaussianCovariance_le_envelope (cell_window hθ)).trans
    ((gaussianEnvelope_mono hθ0 hθ.2 hu).trans (capTable_certificate i hi).upper)

/-- The contract conclusion with larger, certified fallback caps. -/
theorem localCov (i : Fin 60) (θ : ℝ) (hθ : θ ∈ cell i)
    (D : Design 12225) (k : Ret 12225)
    (he : thetaC k.1.2 (D.tau0 k) = θ) (hτ : 0 < D.tau0 k)
    (hC : k ∈ agentEv D (optionBSharp 12225))
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤
      (13 / 10) * (2 / (12225 : ℝ)) / 12225) (v : Fin (mA 12225) → ℝ) :
    Dq k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) v ≤
      capTable i * (2 / (12225 : ℝ)) / 12225 * normSq v := by
  have hw : thetaC k.1.2 (D.tau0 k) ∈ Icc (46 / 100) (528 / 1000) := by
    rw [he]; exact cell_window hθ
  have h := Dq_optionB_gaussian (by norm_num) D k hτ hw hX hC v
  rw [he] at h
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_right _ (normSq_nonneg v)
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 12225)
  exact mul_le_mul_of_nonneg_right (localScalar i hθ) (by norm_num)

theorem localCOV (i : Fin 60) (D : Design 12225) (k : Ret 12225)
    (hθ : thetaC k.1.2 (D.tau0 k) ∈ cell i) (hτ : 0 < D.tau0 k)
    (hC : k ∈ agentEv D (optionBSharp 12225))
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤
      (13 / 10) * (2 / (12225 : ℝ)) / 12225) : COV_at D k (capTable i) :=
  BstLean.Part199.cov_of_scalar (by norm_num) D k hτ le_rfl
    (localCov i _ hθ D k rfl hτ hC hX)

theorem sharp_covariance_event_charge (D : Design 12225) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (optionBSharp 12225))ᶜ ≤ (1 / 4000 : ℝ) :=
  optionB_ret_charge (by norm_num) D hτW

end BstLean.Part254
