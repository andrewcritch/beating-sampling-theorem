import BstLean.Part291FrameScalar
import BstLean.Part291FrameGeometry
import BstLean.Part291SchurCombined
import BstLean.Part291TIEvents
import BstLean.Part291OperatorMoment
import BstLean.Part254GaussianJoint

namespace BstLean.BlueprintLow
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part188 BstLean.Part199 BstLean.Part208 BstLean.Part215 BstLean.Part238 BstLean.Part254
open BstLean.Part150 (thetaC)
open BstLean.Part255 (Parameters)

theorem centreCoordinate_bounded {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n) :
    ∃ K : ℝ, ∀ ξ, |centreCoordinate D c ξ| ≤ K := by
  refine ⟨BstLean.Part229.hiddenScalarConstant c.2.1.1.1 c.2.1.1.2 1 (coordinateVector D c),?_⟩
  intro ξ
  rw [← coordinate_as_sphereScalar]
  exact BstLean.Part229.hiddenScalar_bound _ _ (by norm_num) _ _
    (by rw [nrm,normSq_sphPt hn]; norm_num)

theorem lowFrame_shell_bound {n : ℕ} {p : Parameters} {lo hi θ : ℝ}
    (S : LowTISupply n p lo hi) (hw : θ ∈ Icc lo hi) :
    θ * p.wLam / (1 - radiusMinus n θ lowCoreWindow) * gaussianPair lowCoreWindow +
      θ * p.wLam / (1 - radiusMinus n θ lowWideWindow) * gaussianOutside lowCoreWindow ≤
        lowFrameShell θ p := by
  have hθ0 := (S.core_guard θ hw).theta_nonneg
  have hwd := sub_pos.mpr S.valid.wRadius_lt
  have hcd := sub_pos.mpr S.valid.cRadius_lt
  have hwr := S.wide_radius θ hw
  have hcr := S.core_radius θ hw
  have hw0 := S.valid.wLam_nonneg
  have hpair0 : 0 ≤ gaussianPair lowCoreWindow := gaussianTail_nonneg _
  have hout0 : 0 ≤ gaussianOutside lowCoreWindow := add_nonneg (gaussianTail_nonneg _) (by positivity)
  unfold lowFrameShell
  gcongr

theorem lowFrame_covariance {n : ℕ} (hn : 8000 ≤ n) (D : Design n) (c : Ret n)
    {p : Parameters} {lo hi : ℝ} (S : LowTISupply n p lo hi)
    (hw : thetaC c.1.2 (D.tau0 c) ∈ Icc lo hi) (hτ : 0 < D.tau0 c)
    (hC : ((c.1.2,D.tau0 c),c.2.1.1) ∈ lowSchurEvent n p lo hi)
    (hX : Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 1.269 * (2 / (n : ℝ)) / n) :
    COV_at D c (lowFrameCov n (thetaC c.1.2 (D.tau0 c)) p) := by
  let θ := thetaC c.1.2 (D.tau0 c)
  have hθ0 := (S.core_guard θ hw).theta_nonneg
  have hθ1 := (S.core_guard θ hw).theta_lt_one
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hden : 0 < 1 - 4 * θ / (n : ℝ) := by
    have : 4 * θ / (n : ℝ) < 1 := (div_lt_one hn0).mpr (by linarith)
    linarith
  have hc := ne_zero_of_thetaC_lt (by omega : 0 < n) hτ hθ1
  obtain ⟨hcau,ha,hu⟩ := centre_decomp hc
  have hb : sharpBadMass n lowWideWindow lowCoreWindow p.wLam p.cE p.o p.cS p.chi
      ((c.1.2,D.tau0 c),c.2.1.1) ≤ BstLean.Part255.delta / 0.00025 := by
    exact hC.resolve_left (not_not.mpr hw)
  let K := min (sharpK p.cE p.o p.cS
    (chiCore n (nrm c.1.2) (D.tau0 c) lowCoreWindow.t lowCoreWindow.z 0 p.chi))
    (ta_lam p.cE p.o p.cS)
  have hK : K ≤ p.cLam := (min_le_right _ _).trans S.valid.core_lam
  have hscalar : gaussianScalar n θ lowWideWindow lowCoreWindow K p.wLam
      (1 - 4 * θ / n)⁻¹ 1.269
      (gaussianTail lowWideWindow.pair + 2 * (BstLean.Part255.delta / 0.00025)) ≤
      lowFrameCov n θ p := by
    have h1 := gaussianScalar_mono_K (n := n) (w₀ := lowWideWindow) (w₁ := lowCoreWindow)
      (lam := p.wLam) (M := 1.269)
      (h := gaussianTail lowWideWindow.pair + 2 * (BstLean.Part255.delta / 0.00025))
      hθ0 (inv_nonneg.mpr hden.le) hK
    apply h1.trans
    have hs := lowFrame_shell_bound S hw
    unfold gaussianScalar lowFrameCov lowFrameBad radiusCoefficient
    norm_num only [Nat.cast_ofNat]
    convert add_le_add (add_le_add le_rfl hs) le_rfl using 1 <;> ring
  apply cov_of_scalar (by omega) D c hτ hscalar
  intro v
  exact Dq_gaussian_joint (by omega) c.2.1.1.1 c.2.1.1.2 c.1.2 (uC c.1.2)
    hcau ha hu hτ lowWideWindow lowCoreWindow lowWindows_order
    S.valid.cE_nonneg S.valid.o_nonneg S.valid.cS_nonneg S.valid.wLam_nonneg (by norm_num)
    hθ1 (S.wide_guard θ hw).radius_lt_one (S.core_guard θ hw).radius_lt_one
    (lowCoreRadius_positive hn _ hτ)
    (pow_lt_one₀ S.valid.chi_nonneg S.valid.chi_lt (by norm_num)) (by norm_num : (0 : ℝ) ≤ 1)
    (fun _ _ => sq_nonneg _) hb hX v

theorem lowFrame_weightedSchur {n : ℕ} (hn : 8000 ≤ n) (D : Design n) (c : Ret n)
    {p : Parameters} {lo hi E : ℝ} (S : LowTISupply n p lo hi)
    (hw : thetaC c.1.2 (D.tau0 c) ∈ Icc lo hi) (hτ : 0 < D.tau0 c)
    (hb : 0 < normSq (D.bA c.1 c.2.1.1)) (hb0 : ∀ j, 0 ≤ D.bA c.1 c.2.1.1 j)
    (hI : WFInterfaces D c agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap)
    (hE : centreEnergy D c ≤ E)
    (hY : 0.216 < (1 - 0.0045) ^ 2 - lowFrameMean n E ^ 2)
    (hC : ((c.1.2,D.tau0 c),c.2.1.1) ∈ lowSchurEvent n p lo hi)
    (hX : Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 1.269 * (2 / (n : ℝ)) / n)
    (v : Fin (mA n) → ℝ) :
    (∫ ξ, (wN c.1.2 (D.tau0 c) ξ * weightSq ((1 - 0.0045) ^ 2) 0.216 (centreCoordinate D c ξ)) *
      normSq (vecMul v (BJ c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ξ)) ∂stdGauss (Fin n)) ≤
      lowFrameSchur n (thetaC c.1.2 (D.tau0 c)) p E * normSq v := by
  let θ := thetaC c.1.2 (D.tau0 c)
  let μ := lowFrameMean n E
  let s := √(agentDirectionCap / n)
  let Y := (1 - 0.0045) ^ 2 - μ ^ 2
  let Δ := rwDelta ((1 - 0.0045) ^ 2) 0.216 μ s
  let Ew := ∫ ξ, wN c.1.2 (D.tau0 c) ξ ∂stdGauss (Fin n)
  have hθ0 := (S.core_guard θ hw).theta_nonneg
  have hθ1 := (S.core_guard θ hw).theta_lt_one
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hden : 0 < 1 - 6 * θ / (n : ℝ) := by
    have : 6 * θ / (n : ℝ) < 1 := (div_lt_one hn0).mpr (by linarith)
    linarith
  have hR20 : 0 ≤ radiusCoefficient n 2 θ := by
    unfold radiusCoefficient; norm_num only [Nat.cast_ofNat]; exact div_nonneg hθ0 hden.le
  have hμ0 : 0 ≤ μ := by dsimp [μ,lowFrameMean]; positivity
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have hY0 : 0 < Y := lt_trans (by norm_num) hY
  have hΔ0 : 0 ≤ Δ := by
    dsimp [Δ,rwDelta,rwD2,rwD4]
    have := BstLean.Part195.rotationConstant_nonneg 2
    positivity
  have he0 : 0 ≤ Ew := integral_nonneg (wN_nonneg _ _)
  have he := radius_weight_first (by omega : 7 ≤ n) c.1.2 hτ
  have hwr : 0 ≤ Ew / Y + Δ * (radiusCoefficient n 2 θ / n) := by positivity
  have hc := ne_zero_of_thetaC_lt (by omega : 0 < n) hτ hθ1
  obtain ⟨hcau,ha,hu⟩ := centre_decomp hc
  obtain ⟨Kf,hfK⟩ := centreCoordinate_bounded (by omega) D c
  have hmean0 : 0 ≤ ∫ ξ, centreCoordinate D c ξ ∂stdGauss (Fin n) :=
    integral_nonneg (centreCoordinate_nonneg D c hb0)
  have hmean : (∫ ξ, centreCoordinate D c ξ ∂stdGauss (Fin n)) ≤ μ := by
    have h1 := (abs_le.mp hI.parallel.2).2
    have h2 := sqrt_le_sqrt hE
    dsimp [μ,lowFrameMean]
    linarith
  have hD := rw_deficit_network (by omega) D c hτ hb hI.direction hmean0 hmean
  have hbad : sharpBadMass n lowWideWindow lowCoreWindow p.wLam p.cE p.o p.cS p.chi
      ((c.1.2,D.tau0 c),c.2.1.1) ≤ BstLean.Part255.delta / 0.00025 :=
    hC.resolve_left (not_not.mpr hw)
  have h := weighted_sharp_joint (by omega) c.2.1.1.1 c.2.1.1.2 c.1.2 (uC c.1.2)
    hcau ha hu hτ lowWideWindow lowCoreWindow lowWindows_order
    S.valid.cE_nonneg S.valid.o_nonneg S.valid.cS_nonneg S.valid.wLam_nonneg (by norm_num)
    hθ1 (S.wide_guard θ hw).radius_lt_one (S.core_guard θ hw).radius_lt_one
    (lowCoreRadius_positive hn _ hτ)
    (pow_lt_one₀ S.valid.chi_nonneg S.valid.chi_lt (by norm_num)) (by norm_num : (0 : ℝ) ≤ 1)
    (fun _ _ => sq_nonneg _) hbad hX (centreCoordinate D c) (measurable_centreCoordinate D c)
    (by norm_num : (0 : ℝ) < 0.216) hY hμ0 hs0 (div_nonneg hR20 hn0.le) hfK
    (radius_weight_second (by omega) c.1.2 hτ) hD v
  dsimp only at h
  have hcore (T : ℝ) : (n : ℝ) * min
      (p.cE * (Ew / Y + Δ * (radiusCoefficient n 2 θ / n)) +
        2 * p.o * √((Ew / Y + Δ * (radiusCoefficient n 2 θ / n)) * T) + p.cS * T)
      (ta_lam p.cE p.o p.cS * (Ew / Y + Δ * (radiusCoefficient n 2 θ / n))) ≤
      p.cLam * (radiusCoefficient n 1 θ / Y + Δ * radiusCoefficient n 2 θ) := by
    calc
      _ ≤ (n : ℝ) * (p.cLam * (radiusCoefficient n 1 θ / n / Y +
          Δ * (radiusCoefficient n 2 θ / n))) := by
        apply mul_le_mul_of_nonneg_left _ hn0.le
        apply (min_le_right _ _).trans
        exact mul_le_mul S.valid.core_lam (by gcongr) hwr S.valid.cLam_nonneg
      _ = _ := by field_simp <;> ring
  have hshell := lowFrame_shell_bound S hw
  have heq : (∫ ξ, (wN c.1.2 (D.tau0 c) ξ * weightSq ((1 - 0.0045) ^ 2) 0.216 (centreCoordinate D c ξ)) *
      normSq (vecMul v (BJ c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ξ)) ∂stdGauss (Fin n)) =
      ∫ ξ, weightSq ((1 - 0.0045) ^ 2) 0.216 (centreCoordinate D c ξ) *
        (wN c.1.2 (D.tau0 c) ξ * normSq (vecMul v (BJ c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ξ)))
          ∂stdGauss (Fin n) := by
    apply integral_congr_ae
    exact ae_of_all _ fun _ => by ring
  rw [heq]
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (normSq_nonneg v)
  unfold lowFrameSchur lowFrameBad
  exact add_le_add (hcore _) (div_le_div_of_nonneg_right (add_le_add hshell le_rfl) (by norm_num))

end BstLean.BlueprintLow
