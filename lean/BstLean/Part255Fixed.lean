import BstLean.Part255Symmetry
import BstLean.Part254Interface

namespace BstLean.Part255
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part208 BstLean.Part238 BstLean.Part251 BstLean.Part249 BstLean.Part254
open BstLean.Part199 (exampleWide exampleCore example_nested radiusMinus)
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nrm Xi4)

noncomputable def fixedGaussianSingle (n : ℕ) (θ : ℝ) : ℝ :=
  gaussianScalar n θ exampleWide exampleCore fixedCore (67/100)
    (1-4*θ/n)⁻¹ (13/10)
    (gaussianTail exampleWide.pair + optionBDelta n / (1/4000))

theorem Dq_optionB_single {n : ℕ} (hn : 11883 ≤ n) (D : Design n) (k : Ret n)
    (hτ : 0 < D.tau0 k)
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Icc (46 / 100) (528 / 1000))
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤ (13 / 10) * (2 / (n : ℝ)) / n)
    (hC : k ∈ agentEv D (optionBSharp n)) (v : Fin (mA n) → ℝ) :
    Dq k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) v ≤
      fixedGaussianSingle n (thetaC k.1.2 (D.tau0 k)) * (2 / (n : ℝ)) / n * normSq v := by
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
  have hd := Dq_gaussian_symmetric (by omega : 6 ≤ n) k.2.1.1.1 k.2.1.1.2
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

theorem fixedGaussianSingle_le_envelope {θ : ℝ}
    (hw : θ ∈ Icc (46 / 100) (528 / 1000)) :
    fixedGaussianSingle 12225 θ ≤ gaussianEnvelope θ - (92092/10^9 : ℝ) := by
  have hθ0 : 0 ≤ θ := by linarith [hw.1]
  obtain ⟨hm, hc, hwide⟩ := envelope_denominators hw.2
  obtain ⟨hrw, hrc⟩ := radius_envelope hθ0
  have hwi : (1 - radiusMinus 12225 θ exampleWide)⁻¹ ≤
      (1 - radiusEnvelope θ true)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hwide (by linarith)
  have hci : (1 - radiusMinus 12225 θ exampleCore)⁻¹ ≤
      (1 - radiusEnvelope θ false)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hc (by linarith)
  have hk := mul_le_mul_of_nonneg_right fixedCore_enclosure.2
    (inv_nonneg.mpr hm.le)
  have hp := mul_le_mul
    (mul_le_mul_of_nonneg_left hci (by norm_num : (0 : ℝ) ≤ 67 / 100))
    gaussian_core_pair_upper (by exact gaussianTail_nonneg _)
    (by positivity : 0 ≤ (67 / 100 : ℝ) * (1 - radiusEnvelope θ false)⁻¹)
  have ho := mul_le_mul
    (mul_le_mul_of_nonneg_left hwi (by norm_num : (0 : ℝ) ≤ 67 / 100))
    gaussian_core_outside_upper (by exact add_nonneg (gaussianTail_nonneg _) (by positivity))
    (by positivity : 0 ≤ (67 / 100 : ℝ) * (1 - radiusEnvelope θ true)⁻¹)
  have hs := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hk hp) ho) hθ0
  have he := mul_le_mul_of_nonneg_left
    (gaussian_exceptional_single
      (BstLean.Part249.optionB_cutoff (by norm_num : 11883 ≤ 12225)))
    (by norm_num : (0 : ℝ) ≤ 13 / 10)
  unfold fixedGaussianSingle gaussianScalar gaussianEnvelope
  convert add_le_add hs he using 1 <;>
    simp only [div_eq_mul_inv, Nat.cast_ofNat] <;> ring

noncomputable def capTable (i : Fin 60) : ℝ := by
  classical
  exact if Needed i then BstLean.Part254.capTable i - 92092/10^9 else 0

theorem capTable_improvement (i : Fin 60) (hi : Needed i) :
    BstLean.Part254.capTable i - capTable i = (92092/10^9 : ℝ) := by
  rw [capTable,if_pos hi]
  ring

theorem fixedLocalScalar (i : Fin 60) {θ : ℝ} (hθ : θ ∈ cell i) :
    fixedGaussianSingle 12225 θ ≤ capTable i := by
  have hi := cell_needed hθ
  have hu : cellUpper i ≤ (528/1000 : ℝ) :=
    (min_le_right _ _).trans (by norm_num [worldUpper])
  have hθ0 : 0 ≤ θ := by linarith [(cell_window hθ).1]
  rw [capTable,if_pos hi]
  exact (fixedGaussianSingle_le_envelope (cell_window hθ)).trans
    (sub_le_sub_right ((gaussianEnvelope_mono hθ0 hθ.2 hu).trans
      (capTable_certificate i hi).upper) _)

theorem fixedLocalCov : BstLean.Part253.LocalCovariance BstLean.Part254.cell capTable := by
  intro i θ hn hi k he hτ hC hX v
  have hw : thetaC k.1.2 ((BstLean.Part169.paperDesignP 12225).tau0 k) ∈
      Icc (46/100) (528/1000) := by
    rw [he]
    exact cell_window hi
  have h := Dq_optionB_single (by norm_num) (BstLean.Part169.paperDesignP 12225)
    k hτ hw hX hC v
  rw [he] at h
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_right _ (normSq_nonneg v)
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 12225)
  exact mul_le_mul_of_nonneg_right (fixedLocalScalar i hi) (by norm_num)

end BstLean.Part255
