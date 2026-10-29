import BstLean.Part227Package

/-! Grouped payments replace three separate hidden payments. -/
namespace BstLean.Part233
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part134 BstLean.Part136 BstLean.Part137
open BstLean.Part140 BstLean.Part157 BstLean.Part159 BstLean.Part227
open BstLean.Part143

def distanceGroup (n : ℕ) (Xc : ℝ) : Set (WHid n) :=
  (goodDist n Xc ∩ goodS n) ∩ goodAo n

lemma distanceGroup_meas {n : ℕ} (hn : 1 ≤ n) (Xc : ℝ) :
    MeasurableSet (distanceGroup n Xc) :=
  ((goodDist_meas hn Xc).inter measurableSet_goodS).inter measurableSet_goodAo

noncomputable def groupedCharge (n : ℕ) (sp p₂ dT eB groupPayment : ℝ) : ℝ :=
  372 / 1000 * sp ^ 2 + 448 / 1000 * p₂ + groupPayment +
    4465 / 1000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / ((n : ℝ) * dT) +
    (1716 / 1000) ^ 2 / ((mW n : ℝ) * eB ^ 2)

/-- The same six-factor hidden event uses one grouped payment. -/
theorem hidden_charge_of_group {n : ℕ} (hn : 4096 ≤ n)
    {sp p₂ Xc dT eB groupPayment : ℝ} (hsp : 0 < sp) (hp₂ : 0 < p₂)
    (hdT : 0 < dT) (heB : 0 < eB)
    (hgroup : (hidGauss (2 * n) (mW n)).real (distanceGroup n Xc)ᶜ ≤ groupPayment) :
    (hidGauss (2 * n) (mW n)).real (hidden n sp p₂ Xc dT eB)ᶜ ≤
      groupedCharge n sp p₂ dT eB groupPayment := by
  have hsub : (hidden n sp p₂ Xc dT eB)ᶜ ⊆
      (((goodHid (2 * n) (mW n) (sp ^ 2) p₂)ᶜ ∪ (distanceGroup n Xc)ᶜ) ∪
        (goodT n dT)ᶜ) ∪ (goodB n eB)ᶜ := by
    intro θ hθ
    by_contra h
    have hp : θ ∈ hidden n sp p₂ Xc dT eB := by
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at h
      exact ⟨⟨⟨⟨⟨h.1.1.1, h.1.1.2.1.1⟩, h.1.2⟩, h.1.1.2.1.2⟩,
        h.1.1.2.2⟩, h.2⟩
    exact hθ hp
  have hu := measureReal_union_le (μ := hidGauss (2 * n) (mW n))
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((hu _ _).trans (add_le_add
      ((hu _ _).trans (add_le_add
        ((hu _ _).trans (add_le_add (goodHid_charge hn hsp hp₂) hgroup))
          (goodT_prob143 hn hdT))) (goodB_charge hn heB)))

/-- The retained projection has the same payment, without an extra first-layer event. -/
theorem retained_hidden_charge_of_group {n : ℕ} (hn : 4096 ≤ n) (D : Centres n)
    {sp p₂ Xc dT eB groupPayment : ℝ} (hsp : 0 < sp) (hp₂ : 0 < p₂)
    (hdT : 0 < dT) (heB : 0 < eB)
    (hgroup : (hidGauss (2 * n) (mW n)).real (distanceGroup n Xc)ᶜ ≤ groupPayment) :
    (retDist D).real (Hof (hidden n sp p₂ Xc dT eB))ᶜ ≤
      groupedCharge n sp p₂ dT eB groupPayment := by
  rw [hid_charge D (hidden_meas (by omega) _ _ _ _ _)]
  exact hidden_charge_of_group hn hsp hp₂ hdT heB hgroup

/-- Change only the payment of an already proved World package. -/
noncomputable def rechargedWorld {n : ℕ} {P : BstLean.Part192.Program n}
    {p : BstLean.Part192.WorldParameters} (W : BstLean.Part192.WorldPackage P p)
    (δ : ℝ) (hδ : (hidGauss (2 * n) (mW n)).real W.hiddenᶜ ≤ δ) :
    BstLean.Part192.WorldPackage P {p with hiddenCharge := δ} :=
  { W with hidden_charge := hδ }

theorem rechargedWorld_hidden {n : ℕ} {P : BstLean.Part192.Program n}
    {p : BstLean.Part192.WorldParameters} (W : BstLean.Part192.WorldPackage P p)
    (δ : ℝ) (hδ : (hidGauss (2 * n) (mW n)).real W.hiddenᶜ ≤ δ) :
    (rechargedWorld W δ hδ).hidden = W.hidden := rfl

/-- Replacing the payment preserves the original restricted moment. -/
theorem rechargedWorld_moment {n : ℕ} {P : BstLean.Part192.Program n}
    {p : BstLean.Part192.WorldParameters} (W : BstLean.Part192.WorldPackage P p)
    (δ : ℝ) (hδ : (hidGauss (2 * n) (mW n)).real W.hiddenᶜ ≤ δ) :
    ∫ c in Hof (rechargedWorld W δ hδ).hidden, HbarW P.design c ^ 2
      ∂retDist P.design.toCentres ≤ p.moment := W.restricted_moment

end BstLean.Part233
#print axioms BstLean.Part233.hidden_charge_of_group
#print axioms BstLean.Part233.retained_hidden_charge_of_group
#print axioms BstLean.Part233.rechargedWorld
#print axioms BstLean.Part233.rechargedWorld_moment
