import BstLean.Part192Interfaces

/-! Part 192: the checked World package at 16 200.
The constants retain their existing meanings and dimension hypotheses. -/

namespace BstLean.Part192
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part159
open BstLean.Part169 (paperDesignP)

noncomputable def world16200Parameters : WorldParameters where
  hiddenCharge := BstLean.Part188.Base159_R.δPap
  frame := BstLean.Part156.cWL
  moment := BstLean.Part188.Base159_R.vPap
  productLo := 1994 / 1000
  productHi := 2057 / 1000
  noiseLo := 465 / 1000
  noiseHi := 528 / 1000

noncomputable def world16200 {n : ℕ} (hn : 16200 ≤ n) :
    WorldPackage (paperProgram n) world16200Parameters := by
  have hn1 : 1 ≤ n := by omega
  have hC := constC (n := n) (by omega)
  have hK := constK (n := n) (by omega)
  have hworld := BstLean.Part188.Base159_R.paper_world hn (paperDesignP n)
    rfl (fun _ => rfl)
  have hev := hworld.1 (E₁ := Set.univ) MeasurableSet.univ
    (δextra := 0) (by simp)
  refine {
    hidden := GPap n
    hidden_measurable := measurableSet_GPap hn1
    scale := tau0p
    scale_measurable := measurable_tau0p
    scale_eq := fun _ => rfl
    calibration := ccP n
    calibration_measurable := measurable_ccP
    hidden_charge := BstLean.Part188.Base159_R.pap_charge hn
    product_window := ?_
    scale_identity := ?_
    lowerEvent := Ethm (paperCentres n)
    upperEvent := Ethp (paperCentres n)
    lower_measurable := measurableSet_Ethm _
    upper_measurable := measurableSet_Ethp _
    noise_window := ?_
    frame_bound := hworld.2 (E := Hof (GPap n)) (fun _ hc => hc)
    moment_integrable := hev.2.2.2.2.1
    restricted_moment := hev.2.2.2.2.2.1 }
  · intro θ hθ
    exact (BstLean.Part188.Base159_R.pap_window hn hC hK hθ).2
  · intro θ hθ
    have ht := BstLean.Part188.Base159_R.pap_tau hn hC hK hθ
    exact ⟨ht.2, ht.1⟩
  · intro c hc
    obtain ⟨_, _, _, _, hlo, hhi⟩ :=
      BstLean.Part188.Base159_R.theta_window_paper' hn (paperDesignP n)
        rfl (fun _ => rfl) hc.1
    have he := BstLean.Part160.thetaIn_eq (paperDesignP n) c
    exact ⟨he ▸ hlo hc.2.1, he ▸ hhi hc.2.2⟩

/-- The hidden charge transfers without an additional payment. -/
theorem world_retained_charge {n : ℕ} {P : Program n} {p : WorldParameters}
    (W : WorldPackage P p) :
    (retDist P.design.toCentres).real (Hof W.hidden)ᶜ ≤ p.hiddenCharge := by
  rw [hid_charge P.design.toCentres W.hidden_measurable]
  exact W.hidden_charge

/-- The restricted radius uses the same centre and scalar as the hidden package. -/
theorem world_radius_identity {n : ℕ} {P : Program n} {p : WorldParameters}
    (W : WorldPackage P p) (c : Ret n) :
    HbarW P.design c ^ 2 = hellHid P.design.bW W.scale c.1.1 := by
  rw [HbarW_sq]
  exact HbarW2_eq_hellHid P.design c (W.scale_eq c)

/-- A retained event charge is a separate input; the hidden payment occurs once. -/
theorem world_events {n : ℕ} {P : Program n} {p : WorldParameters}
    (W : WorldPackage P p) {E : Set (Ret n)} (hE : MeasurableSet E) {δ : ℝ}
    (hδ : (retDist P.design.toCentres).real (Hof W.hidden ∩ Eᶜ) ≤ δ) :
    EVENTS_hyp P.design.toCentres (Hof W.hidden) E (HbarW P.design)
      p.hiddenCharge p.moment δ :=
  ⟨measurableSet_Hof W.hidden_measurable, hE, measurable_HbarW P.design,
    world_retained_charge W, W.moment_integrable, W.restricted_moment, hδ⟩

end BstLean.Part192
#print axioms BstLean.Part192.world16200
#print axioms BstLean.Part192.world_retained_charge
#print axioms BstLean.Part192.world_radius_identity
#print axioms BstLean.Part192.world_events
