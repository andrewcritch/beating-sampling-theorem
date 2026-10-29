import BstLean.Part227Frame
import BstLean.Part227Charge
import BstLean.Part227Noise
import BstLean.Part192World

/-! Part 227: the parameterized World package for the unchanged exact-moment program. -/
namespace BstLean.Part227
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part134 BstLean.Part136 BstLean.Part137
open BstLean.Part140 BstLean.Part157 BstLean.Part159 BstLean.Part192

noncomputable def worldParameters {n : ℕ} {sp p₂ Xc dT eB : ℝ}
    (c : FrameCertificate n sp p₂ Xc dT eB) (distancePayment Alo Ahi ζ : ℝ) : WorldParameters where
  hiddenCharge := hiddenChargeWithDistance n sp p₂ dT eB distancePayment
  frame := frameValue c
  moment := momentValue n Alo Ahi ζ
  productLo := Alo
  productHi := Ahi
  noiseLo := noiseLower Alo
  noiseHi := noiseUpper n Ahi

/-- Scalar certificates supply all analytic fields of the World package from 4096. -/
noncomputable def worldPackage {n : ℕ} (hn : 4096 ≤ n)
    {sp p₂ Xc dT eB distancePayment Alo Ahi ζ : ℝ}
    (hsp : 4 / 100 ≤ sp) (hp₂ : 4 / 10000 ≤ p₂)
    (hDist : (hidGauss (2 * n) (mW n)).real (goodDist n Xc)ᶜ ≤ distancePayment)
    (hXc : Xc ≤ 3 / 4) (hdT0 : 0 < dT) (hdT : dT ≤ 1 / 400000) (heB : 0 < eB)
    (c : FrameCertificate n sp p₂ Xc dT eB)
    (hk : kernelError n < kap1 (2 * n))
    (hAlo : 1 < Alo) (hlo : Alo ≤ productLower n eB)
    (hhi : productUpper n eB ≤ Ahi) (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    WorldPackage (paperProgram n) (worldParameters c distancePayment Alo Ahi ζ) := by
  let G := hidden n sp p₂ Xc dT eB
  have mG : MeasurableSet G := hidden_meas (by omega) _ _ _ _ _
  have hG : G ⊆ (goodB n eB ∩ goodS n) ∩ goodAo n :=
    fun _ h => ⟨⟨h.2, h.1.1.2⟩, h.1.2⟩
  have hm := retained_moment hn (paperProgram n).design rfl (fun _ => rfl)
    mG hG c.norm_lower c.norm_separation.le hk hAlo hlo hhi hζ0 hζ1
  refine {
    hidden := G
    hidden_measurable := mG
    scale := tau0p
    scale_measurable := measurable_tau0p
    scale_eq := fun _ => rfl
    calibration := ccP n
    calibration_measurable := measurable_ccP
    hidden_charge := hidden_charge_of_distance hn (by linarith) (by linarith) hdT0 heB hDist
    product_window := ?_
    scale_identity := ?_
    lowerEvent := Ethm (paperProgram n).design.toCentres
    upperEvent := Ethp (paperProgram n).design.toCentres
    lower_measurable := measurableSet_Ethm _
    upper_measurable := measurableSet_Ethp _
    noise_window := ?_
    frame_bound := retained_frame hn (paperProgram n).design.toCentres rfl
      hsp hp₂ hXc hdT0.le hdT c (fun _ h => h)
    moment_integrable := hm.1
    restricted_moment := hm.2 }
  · intro θ hθ
    have hp := hG hθ
    obtain ⟨hl, hu⟩ := product_window hn hp.1.1 hp.1.2 hp.2
      c.norm_lower c.norm_separation.le hk
    exact ⟨hlo.trans hl, hu.trans hhi⟩
  · intro θ hθ
    have hp := hG hθ
    exact scale_identity hn hp.1.1 hp.1.2 hp.2 c.norm_lower c.norm_separation.le hk hAlo hlo
  · intro x hx
    have hp := hG hx.1
    exact noise_window hn (paperProgram n).design rfl (fun _ => rfl)
      hp.1.1 hp.1.2 hp.2 c.norm_lower c.norm_separation.le hk hAlo hlo hhi hx.2.1 hx.2.2

/-- The two retained angle events have their original payments. -/
theorem retained_angle_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) {G : Set (WHid n)} :
    (retDist D).real (Hof G ∩ (Ethm D ∩ Ethp D)ᶜ) ≤
      exp (-(45 / 10000 * (n : ℝ))) + exp (-12) := by
  have hsub : Hof G ∩ (Ethm D ∩ Ethp D)ᶜ ⊆ (Ethm D)ᶜ ∪ (Ethp D)ᶜ := by
    intro x hx
    simpa only [Set.mem_compl_iff, Set.mem_inter_iff, not_and_or, Set.mem_union] using hx.2
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (ethm_charge D) (ethp_charge hn D)))

/-- The master event interface pays the hidden event once and the angle events separately. -/
theorem world_angle_events {n : ℕ} (hn : 1 ≤ n) {P : Program n} {p : WorldParameters}
    (W : WorldPackage P p) :
    EVENTS_hyp P.design.toCentres (Hof W.hidden)
      (Ethm P.design.toCentres ∩ Ethp P.design.toCentres) (HbarW P.design)
      p.hiddenCharge p.moment (exp (-(45 / 10000 * (n : ℝ))) + exp (-12)) :=
  BstLean.Part192.world_events W
    ((measurableSet_Ethm _).inter (measurableSet_Ethp _)) (retained_angle_charge hn _)

end BstLean.Part227
#print BstLean.Part227.worldPackage
#print axioms BstLean.Part227.worldPackage
#print axioms BstLean.Part227.retained_angle_charge
#print axioms BstLean.Part227.world_angle_events
