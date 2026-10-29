import BstLean.Part271R3Bounds
import BstLean.Part227Guards
import BstLean.Part197Log

/-! A scalar interface for banded variant-E World packages. -/
namespace BstLean.Part271.R3
open Real MeasureTheory Set BstLean.Part130 BstLean.Part137 BstLean.Part140
open BstLean.Part157 BstLean.Part159 BstLean.Part192 BstLean.Part218 BstLean.Part227

/-- Relax scalar allowances without changing the events, centre, or calibration. -/
noncomputable def relaxWorld {n : ℕ} {P : Program n} {p q : WorldParameters}
    (W : WorldPackage P p)
    (hh : p.hiddenCharge ≤ q.hiddenCharge) (hf : p.frame ≤ q.frame)
    (hm : p.moment ≤ q.moment) (hpl : q.productLo ≤ p.productLo)
    (hpu : p.productHi ≤ q.productHi) (hnl : q.noiseLo ≤ p.noiseLo)
    (hnu : p.noiseHi ≤ q.noiseHi) : WorldPackage P q where
  hidden := W.hidden
  hidden_measurable := W.hidden_measurable
  scale := W.scale
  scale_measurable := W.scale_measurable
  scale_eq := W.scale_eq
  calibration := W.calibration
  calibration_measurable := W.calibration_measurable
  hidden_charge := W.hidden_charge.trans hh
  product_window := fun θ hθ =>
    ⟨hpl.trans (W.product_window θ hθ).1, (W.product_window θ hθ).2.trans hpu⟩
  scale_identity := W.scale_identity
  lowerEvent := W.lowerEvent
  upperEvent := W.upperEvent
  lower_measurable := W.lower_measurable
  upper_measurable := W.upper_measurable
  noise_window := fun c hc =>
    ⟨hnl.trans (W.noise_window c hc).1, (W.noise_window c hc).2.trans hnu⟩
  frame_bound := by
    intro c hc w
    apply (W.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right hf (Nat.cast_nonneg n)
  moment_integrable := W.moment_integrable
  restricted_moment := W.restricted_moment.trans hm

/-- Every field is an explicit scalar inequality. No network supply is an input. -/
structure WorldCertificate (n : ℕ) (p : WorldParameters) where
  frameCertificate : FrameCertificate n (44945 / 10^6) (4 / 10000)
    (712 / 10000) (178 / 10^8) (1232 / 10^7)
  delta : ℝ
  distance : ℝ
  delta_nonneg : 0 ≤ delta
  mean_bound : e1MeanBound (2*n) (mW n) (1/10^6) (1/10^7) BstLean.Part250.rowEps ≤ delta
  reserve : ((2*n : ℕ) : ℝ) * (1+1/10^6) * delta < 712/10000
  distance_bound : directDistancePayment n (1/10^6) (1/10^7) delta (712/10000)
    BstLean.Part250.rowEps ≤ distance
  product_lower : 202225/100000 ≤ productLower n (1232/10^7)
  product_upper : productUpper n (1232/10^7) ≤ 202831/100000
  hidden_bound : hiddenChargeWithDistance n (44945/10^6) (4/10000)
    (178/10^8) (1232/10^7) distance ≤ p.hiddenCharge
  frame_bound : frameValue frameCertificate ≤ p.frame
  moment_bound : momentValue n (202225/100000) (202831/100000) (1/50) ≤ p.moment
  productLo_bound : p.productLo ≤ 202225/100000
  productHi_bound : 202831/100000 ≤ p.productHi
  noiseLo_bound : p.noiseLo ≤ noiseLower (202225/100000)
  noiseHi_bound : noiseUpper n (202831/100000) ≤ p.noiseHi

noncomputable def WorldCertificate.toWorldPackage {n : ℕ} (hn : 4096 ≤ n)
    {p : WorldParameters} (c : WorldCertificate n p) :
    WorldPackage (paperProgram n) p := by
  have hd : (BstLean.Part136.hidGauss (2*n) (mW n)).real
      (goodDist n (712/10000))ᶜ ≤ c.distance := by
    apply le_trans (concrete_distance_charge hn
      (εω := 1/10^6) (ph := 1/10^7) (Δ := c.delta)
      (ε := BstLean.Part250.rowEps) (by norm_num) (by norm_num) (by norm_num)
      (by intro i; fin_cases i <;> norm_num [BstLean.Part250.rowEps])
      c.delta_nonneg c.mean_bound c.reserve)
    exact c.distance_bound
  let W := BstLean.Part227.worldPackage hn
    (sp := 44945/10^6) (p₂ := 4/10000) (Xc := 712/10000)
    (dT := 178/10^8) (eB := 1232/10^7) (distancePayment := c.distance)
    (Alo := 202225/100000) (Ahi := 202831/100000) (ζ := 1/50)
    (by norm_num) (by norm_num) hd (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) c.frameCertificate
    (window_guards hn (eB := 1232/10^7) (by norm_num)).2.2
    (by norm_num) c.product_lower c.product_upper (by norm_num) (by norm_num)
  exact relaxWorld W c.hidden_bound c.frame_bound c.moment_bound
    c.productLo_bound c.productHi_bound c.noiseLo_bound c.noiseHi_bound

theorem WorldCertificate.angle_events {n : ℕ} (hn : 4096 ≤ n)
    {p : WorldParameters} (c : WorldCertificate n p) :
    (c.toWorldPackage hn).lowerEvent = Ethm (paperProgram n).design.toCentres ∧
    (c.toWorldPackage hn).upperEvent = Ethp (paperProgram n).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part271.R3
