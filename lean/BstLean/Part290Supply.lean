import BstLean.Part290Core
import BstLean.Part236RetainedMoments
import BstLean.Part289Design

/-! The grouped World supply, independent of the program's mixture floor. -/
namespace BstLean.Part290
open Real MeasureTheory Set
open BstLean.Part29 (uniformSphere)
open BstLean.Part130 BstLean.Part134 BstLean.Part136 BstLean.Part137
open BstLean.Part140 BstLean.Part157 BstLean.Part159 BstLean.Part192
open BstLean.Part227 BstLean.Part233 BstLean.Part236

def worldHidden (n : ℕ) : Set (WHid n) :=
  hidden n (4/100) (4/10000) (525/10000) (25/10^7) (1232/10^7)

noncomputable def worldParameters {n : ℕ}
    (c : FrameCertificate n (4/100) (4/10000) (525/10000) (25/10^7) (1232/10^7)) :
    WorldParameters :=
  groupedWorldParameters c (805/10^9) (202278/100000) (202798/100000) (22/1000)

noncomputable def groupedPackage {n : ℕ} (ha : 8000 ≤ n) :
    WorldPackage (paperProgram n) (worldParameters (worldFrameCertificate ha)) :=
  worldPackage_of_group (show 4096 ≤ n by omega) (le_refl _) (le_refl _)
    (group_charge ha) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (worldFrameCertificate ha) (window_guards ha).2.2 (by norm_num)
    (product_lower ha) (product_upper ha) (by norm_num) (by norm_num)

/-- This interface states only World facts. It does not require equality of complete programs. -/
structure WorldSupply {n : ℕ} (D : Design n)
    (c : FrameCertificate n (4/100) (4/10000) (525/10000) (25/10^7) (1232/10^7)) : Prop where
  first_layer : FirstLayerSupply n
  kernel_bounds : (49372/100000 : ℝ) ≤ kap1 (2*n) ∧ kap1 (2*n) ≤ 4938/10000
  kernel_error : 0 ≤ kernelError n ∧ kernelError n < kap1 (2*n)
  product_lower : (202278/100000 : ℝ) ≤ productLower n (1232/10^7)
  product_upper : productUpper n (1232/10^7) ≤ 202798/100000
  product_order : 1 < productLower n (1232/10^7) ∧
    productLower n (1232/10^7) ≤ productUpper n (1232/10^7)
  displayed_guards : (46/100 : ℝ) ≤ (productLower n (1232/10^7)-1)/
      (114/100+productLower n (1232/10^7)-1) ∧
    noiseUpper n (productUpper n (1232/10^7)) ≤ 54/100
  frame_caps : frameBase c (1/10^9) (1/10^12) ≤ 419/1000 ∧
    coeffK c (1/10^9) ≤ 1219/10^5 ∧ coeffD c (1/10^9) ≤ 787/10^8
  calibration_bound : BstLean.Part210.Rnew n ≤ 92/10000
  moment_cap : momentValue n (202278/100000) (202798/100000) (22/1000) ≤ 3164/10^11
  radius_pos : 0 < rLowG (202278/100000) (202798/100000) (22/1000)
  historical_window : (977865116059865/10^15 : ℝ) < 202278/100000-1 ∧
    (202798/100000 : ℝ) < 1/(484172857615036/10^15)
  grouped_package : Nonempty (WorldPackage (paperProgram n) (worldParameters c))
  hidden_measurable : MeasurableSet (worldHidden n)
  hidden_charge : (hidGauss (2*n) (mW n)).real (worldHidden n)ᶜ < 1092/10^6
  retained_charge : (retDist D.toCentres).real (Hof (worldHidden n))ᶜ < 1092/10^6
  angle_charge : (retDist D.toCentres).real
      (Hof (worldHidden n) ∩ (Ethm D.toCentres ∩ Ethp D.toCentres)ᶜ) ≤
        exp (-(45/10000*(n : ℝ)))+exp (-12)
  product_window : ∀ θ ∈ worldHidden n,
    (202278/100000 : ℝ) ≤ 2/(mW n : ℝ)*normSq (D.bW θ)*ccP n θ ∧
    2/(mW n : ℝ)*normSq (D.bW θ)*ccP n θ ≤ 202798/100000
  scale_identity : ∀ θ ∈ worldHidden n, 0 < tau0p θ ∧ tau0p θ^2 =
    2/(mW n : ℝ)*normSq (D.bW θ)*(2/(mW n : ℝ)*normSq (D.bW θ)*ccP n θ-1)
  scale_eq : ∀ x, D.tau0 x = tau0p x.1.1
  noise_window : ∀ x ∈ Hof (worldHidden n) ∩ (Ethm D.toCentres ∩ Ethp D.toCentres),
    (472/1000 : ℝ) ≤ BstLean.Part150.thetaC x.1.2 (D.tau0 x) ∧
      BstLean.Part150.thetaC x.1.2 (D.tau0 x) ≤ 528/1000
  replacement_integrable : IntegrableOn (fun x => HbarW D x^2)
    (Hof (worldHidden n)) (retDist D.toCentres)
  replacement_moment : (∫ x in Hof (worldHidden n), HbarW D x^2 ∂retDist D.toCentres) ≤ 3164/10^11
  frame : ∀ θ ∈ worldHidden n, ∀ w : Fin (mW n) → ℝ,
    (∫ u, (∑ j, eDir (D.bW θ) (hid2 θ.1 θ.2 u) j*w j)^2 ∂uniformSphere (2*n)) ≤
      (frameBase c (1/10^9) (1/10^12)+frameError c (1/10^9) θ)/(n : ℝ)*∑ j, w j^2
  error_nonneg : ∀ θ : WHid n, 0 ≤ yK θ ∧ 0 ≤ yD θ
  error_max : ∀ θ ∈ worldHidden n, frameError c (1/10^9) θ ≤
    25*coeffK c (1/10^9)+2500*coeffD c (1/10^9)
  error_moments : ∀ E : Set (Ret n),
    IntegrableOn (fun x : Ret n => (coeffK c (1/10^9)*√(yK x.1.1))^2) E (retDist D.toCentres) ∧
    IntegrableOn (fun x : Ret n => coeffD c (1/10^9)*yD x.1.1) E (retDist D.toCentres) ∧
    (∫ x in E, (coeffK c (1/10^9)*√(yK x.1.1))^2 ∂retDist D.toCentres) ≤
      (372/1000)*coeffK c (1/10^9)^2 ∧
    (∫ x in E, coeffD c (1/10^9)*yD x.1.1 ∂retDist D.toCentres) ≤
      (448/1000)*coeffD c (1/10^9)

theorem worldSupply_of_centres {n : ℕ} (ha : 8000 ≤ n) (D : Design n)
    (hD : D.bW = bWp) (hτ : ∀ x, D.tau0 x = tau0p x.1.1) :
    WorldSupply D (worldFrameCertificate ha) := by
  have hn : 4096 ≤ n := by omega
  have hc := worldFrameCertificate ha
  have hk := window_guards ha
  have hmG : MeasurableSet (worldHidden n) := hidden_meas (by omega) _ _ _ _ _
  have hG : worldHidden n ⊆ (goodB n (1232/10^7) ∩ goodS n) ∩ goodAo n :=
    fun _ h => ⟨⟨h.2,h.1.1.2⟩,h.1.2⟩
  have hcharge : (hidGauss (2*n) (mW n)).real (worldHidden n)ᶜ < 1092/10^6 :=
    (hidden_charge_of_group hn (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (group_charge ha)).trans_lt (hidden_cap ha)
  have hmoment := retained_moment hn D hD hτ hmG hG hk.1 hk.2.1.le hk.2.2
    (by norm_num : (1 : ℝ) < 202278/100000) (product_lower ha) (product_upper ha)
    (by norm_num : (0 : ℝ) < 22/1000) (by norm_num : (22/1000 : ℝ) < 1)
  refine {
    first_layer := firstLayerSupply ha
    kernel_bounds := ⟨(by norm_num : (49372/100000 : ℝ) ≤ _).trans (kernel_window ha).1,
      (kernel_window ha).2.trans (by norm_num)⟩
    kernel_error := ⟨by unfold kernelError; positivity, hk.2.2⟩
    product_lower := product_lower ha
    product_upper := product_upper ha
    product_order := product_order ha
    displayed_guards := displayed_noise_guards ha
    frame_caps := frame_caps ha
    calibration_bound := (calibration_bound ha).2
    moment_cap := moment_cap ha
    radius_pos := by norm_num [rLowG,zetaG]
    historical_window := by norm_num
    grouped_package := ⟨groupedPackage ha⟩
    hidden_measurable := hmG
    hidden_charge := hcharge
    retained_charge := ?_
    angle_charge := retained_angle_charge (by omega) D.toCentres
    product_window := ?_
    scale_identity := ?_
    scale_eq := hτ
    noise_window := ?_
    replacement_integrable := hmoment.1
    replacement_moment := hmoment.2.trans (moment_cap ha)
    frame := ?_
    error_nonneg := fun θ => ⟨yK_nonneg θ,yD_nonneg θ⟩
    error_max := fun θ hθ => frame_error_max hn (worldFrameCertificate ha) (by norm_num) hθ
    error_moments := fun E => retained_error_moments hn D.toCentres
      (worldFrameCertificate ha) (by norm_num) E }
  · rw [hid_charge D.toCentres hmG]
    exact hcharge
  · intro θ hθ
    rw [hD]
    have hp := hG hθ
    obtain ⟨hl,hu⟩ := BstLean.Part227.product_window hn hp.1.1 hp.1.2 hp.2 hk.1 hk.2.1.le hk.2.2
    exact ⟨(product_lower ha).trans hl,hu.trans (product_upper ha)⟩
  · intro θ hθ
    rw [hD]
    have hp := hG hθ
    exact BstLean.Part227.scale_identity hn hp.1.1 hp.1.2 hp.2 hk.1 hk.2.1.le hk.2.2
      (by norm_num) (product_lower ha)
  · intro x hx
    have hp := hG hx.1
    have hw := BstLean.Part227.noise_window hn D hD hτ hp.1.1 hp.1.2 hp.2
      hk.1 hk.2.1.le hk.2.2 (by norm_num : (1 : ℝ) < 202278/100000)
      (product_lower ha) (product_upper ha) hx.2.1 hx.2.2
    exact ⟨(noise_caps ha).1.trans hw.1,hw.2.trans (noise_caps ha).2⟩
  · intro θ hθ w
    rw [hD]
    exact pointwise_frame hn (by norm_num) (by norm_num) (by norm_num)
      (worldFrameCertificate ha) (by norm_num) (by norm_num) hθ w

end BstLean.Part290

namespace BstLean.BlueprintLow

/-- Node 38 on the whole low band, for the revised stated program. -/
theorem worldSupplyBand {n : ℕ} (ha : 8000 ≤ n) (_hb : n ≤ 11882) :
    BstLean.Part290.WorldSupply (BstLean.Part289.statedDesign2 n)
      (BstLean.Part290.worldFrameCertificate ha) :=
  BstLean.Part290.worldSupply_of_centres ha _ rfl (fun _ => rfl)

end BstLean.BlueprintLow
