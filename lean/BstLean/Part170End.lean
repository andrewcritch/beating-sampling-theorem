import BstLean.Part170Ev

/-!
# Part 170 (file `End`): `MomZ` from the bias event; the end theorem with node moments

No proof is left open; no `native_decide` or `axiom` is used.

* **`momZ_of_Ebias`**: on `Ebias Gs A_f A_ω` with the World data in the window, `MomZ c A_f A_ω`
  holds (the kept set is a subset of all indices; `exF⁸ ≥ 0`; integrability from boundedness).
* `windowW_of_goodD`, `Ebias_of_goodD`: the good set gives the window and the bias event.
* **`classifier_paper_node80k`**: the classifier theorem (every `n ≥ 80 000`) with `MomZ` and
  the bias charge removed. Remaining: the node moments `NodeMom Gs F E` on a free measurable
  Agent event family `Gs` with charge `δ_G`, the linear condition `A_ω + 8.06A_f ≤ 0.72`, the
  charge `δ_A` of the caller's `E_A`, and `δ_A + δ_G + (F/A_f)⁸ + (E/A_ω)⁸ ≤ roomE`.
-/

namespace BstLean.Part170

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part153 (nuA)
open BstLean.Part166 (goodD)

variable {n : ℕ}

lemma int_pow8_le_univ {X : Ix n → ℝ} (mX : Measurable X) (hb : ∃ M, ∀ a, |X a| ≤ M)
    (K : Set (Ix n)) : ∫ a in K, X a ^ 8 ∂muI n ≤ ∫ a, X a ^ 8 ∂muI n := by
  obtain ⟨M, hM⟩ := hb
  have hi : Integrable (fun a => X a ^ 8) (muI n) := by
    refine Integrable.mono' (integrable_const (M ^ 8)) (mX.pow_const 8).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM a) 8
  exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun a => by positivity)

/-- **`MomZ` on the bias event** (World data in the window). -/
theorem momZ_of_Ebias (hn : 1 ≤ n) {Gs : Set (WRet n × AHid n)} {Af Aw : ℝ} {c : Ret n}
    (hc : c ∈ Ebias Gs Af Aw) (hw : windowW c.1) : MomZ c Af Aw := by
  obtain ⟨-, hF, hW⟩ := hc hw
  exact ⟨(int_pow8_le_univ (measurable_exF c) (bdd_exF hn c) _).trans hF,
    (int_pow8_le_univ (measurable_exW c) (bdd_exW hn c) _).trans hW⟩

lemma windowW_of_goodD (hn : 16384 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) : windowW c.1 :=
  BstLean.Part164.window_goodA hn passF passW measurable_passF measurable_passW _ c hc

lemma Ebias_of_goodD {EA E : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) (EA ∩ E)) : c ∈ E :=
  hc.2.1.2.1.1.1.1.2

/-- **The classifier theorem with `MomZ` and the bias charge removed** (every `n ≥ 80 000`).
Remaining: the node moments `NodeMom Gs F E` (eighth moments of the exact Gaussian-rule errors
over the Agent hidden matrices, at a fixed World datum in the window and a fixed node,
restricted to the Agent event family `Gs`), the charge `δ_G` of `Gs`, the linear condition,
the charge `δ_A` of the caller's `E_A`, and `δ_A + δ_G + (F/A_f)⁸ + (E/A_ω)⁸ ≤ roomE`. -/
theorem classifier_paper_node80k (hn : 80000 ≤ n) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    {Gs : Set (WRet n × AHid n)} (hG : MeasurableSet Gs) {δG : ℝ}
    (hδG : ∀ wr : WRet n, (nuA n).real {θ | (wr, θ) ∉ Gs} ≤ δG)
    {F E Af Aw : ℝ} (hAf : 0 < Af) (hAw : 0 < Aw) (hlin : Aw + 806 / 100 * Af ≤ 72 / 100)
    (hM : NodeMom Gs F E)
    (hroom : δA + (δG + (F / Af) ^ 8 + (E / Aw) ^ 8) ≤ BstLean.Part167.roomE) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  exact classifier_paper_A80k hn t hEA (measurableSet_Ebias hG Af Aw) hA
    (Ebias_charge hn1 (paperCentres n) hG hAf hAw hM hδG) hroom hAf hAw hlin
    (fun c hc => momZ_of_Ebias hn1 (Ebias_of_goodD hc) (windowW_of_goodD (by omega) hc))

end BstLean.Part170
