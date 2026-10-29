import BstLean.Part256Row
import BstLean.Part256Root

namespace BstLean.Part256
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part192 BstLean.Part196
open BstLean.Part169 (paperDesignP)
open BstLean.Part249
open BstLean.Part253 (SourceEvents)

theorem row_classifier_from_common_base
    (W : WorldPackage (paperProgram 12225)
      (BstLean.Part243.rowWorldParameters BstLean.Part243.proposedHiddenCharge))
    (t : ℝ) {E : Set (Ret 12225)}
    (hE : MeasurableSet E)
    (hcharge : (retDist (paperCentres 12225)).real
      (BstLean.Part159.Hof W.hidden ∩ Eᶜ) ≤ baseChargeAllowance)
    (hwindow : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ BstLean.Part255.selectedGood (paperDesignP 12225)) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius,
      BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ Icc BstLean.Part254.worldLower BstLean.Part254.worldUpper)
    (hsource : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ BstLean.Part255.selectedGood (paperDesignP 12225)) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius, SourceEvents c)
    (hbase : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ BstLean.Part255.selectedGood (paperDesignP 12225))
      (HbarW (paperDesignP 12225)) BstLean.Part243.rowRadius,
      c ∈ BstLean.Part252.hqBaseEvent) :
    99 / 100 ≤ ((mlpTriple 2 12225).prod (sampMeas (10 ^ 12) 12225)).real
      {x | successNet x.1 t (progOut (paperDesignP 12225) t aL (10 ^ 12) x.1 x.2)} := by
  apply row_classifier_selected W t hE hcharge hwindow hsource
  intro c hc
  have F := hsource c hc
  have hθ := hwindow c hc
  have hw := BstLean.Part254.world_window hθ
  have hW : BstLean.Part161.WINDOW (paperDesignP 12225) c :=
    BstLean.Part252.window_of_theta (by norm_num) _ c F.scale_pos
      ⟨hw.1, hw.2.trans (by norm_num)⟩
  have hθs : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
      BstLean.Part253.worldInterval := by
    constructor <;>
      norm_num [BstLean.Part253.worldInterval, BstLean.Part254.worldLower,
        BstLean.Part254.worldUpper] at hθ ⊢ <;> linarith [hθ.1, hθ.2]
  exact ⟨rootInputs_from_source t hW (hbase c hc) F hθs⟩

end BstLean.Part256
