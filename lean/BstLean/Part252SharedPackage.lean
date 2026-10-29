import BstLean.Part252BaseEvent
import BstLean.Part252RootEvent
import BstLean.Part249Bridge

/-! The common event retains the stronger operator source and pays it only once.
The table-event charge, local frame supply and five root remainder bounds remain inputs. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem window_of_theta {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c)
    (hθ : BstLean.Part150.thetaC c.1.2 (D.tau0 c) ∈ Icc (46 / 100) (54 / 100)) :
    WINDOW D c := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * D.tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hτ))
  unfold BstLean.Part150.thetaC BstLean.Part150.rhoC at hθ
  rw [sq_sqrt hden.le] at hθ
  have hlow := (le_div_iff₀ hden).mp hθ.1
  have hhigh := (div_le_iff₀ hden).mp hθ.2
  refine ⟨?_, hτ, hlow, hhigh⟩
  intro hc
  rw [hc] at hhigh
  have hn0 : normSq (0 : Fin n → ℝ) = 0 := by simp [normSq]
  rw [hn0, zero_add] at hhigh
  have hh := mul_pos hnR (sq_pos_of_pos hτ)
  nlinarith

theorem window_of_frame {c : Ret 12225} {cf : ℝ}
    (F : BstLean.Part249.FrameInputs 12225 c cf) : WINDOW (paperDesignP 12225) c :=
  window_of_theta (by norm_num) _ c F.scale_pos
    ⟨F.window.1, F.window.2.trans (by norm_num)⟩

theorem energy_pos_of_frame {c : Ret 12225} {cf : ℝ}
    (F : BstLean.Part249.FrameInputs 12225 c cf) : 0 < eR c := by
  exact div_pos F.centre_pos (by norm_num)

def commonEvent (T : Set (Ret 12225)) : Set (Ret 12225) :=
  baseEvent T ∩ sharedGood (paperDesignP 12225)

theorem commonEvent_measurable {T : Set (Ret 12225)} (hT : MeasurableSet T) :
    MeasurableSet (commonEvent T) :=
  (baseEvent_measurable hT).inter (sharedGood_measurable _)

theorem commonEvent_charge {H T : Set (Ret 12225)}
    (hT : (retDist (paperCentres 12225)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12225)).real (H ∩ (commonEvent T)ᶜ) ≤
      BstLean.Part243.proposedRetainedCharge := by
  have hs : H ∩ (commonEvent T)ᶜ ⊆
      (H ∩ (baseEvent T)ᶜ) ∪ (sharedGood (paperDesignP 12225))ᶜ := by
    intro c hc
    by_cases hb : c ∈ baseEvent T
    · exact Or.inr fun hg => hc.2 ⟨hb, hg⟩
    · exact Or.inl ⟨hc.1, hb⟩
  have hS := sharedGood_charge (by norm_num : 11883 ≤ 12225) (paperDesignP 12225)
    (paperDesign_tauWorld _ _ _ _)
  have hh := (measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (baseEvent_charge hT) hS))
  simpa only [BstLean.Part249.base_charge_restored] using hh

/-- This constructor does not assume `RootInputs` or the replacement conclusion. -/
noncomputable def sharedAgentPackage {H T : Set (Ret 12225)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12225)).real (H ∩ Tᶜ) ≤ tableChargeAllowance)
    (t : ℝ)
    (hframe : ∀ c ∈ goodSet H (commonEvent T) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius,
      Nonempty (BstLean.Part249.FrameInputs 12225 c BstLean.Part249.optionBAgentFrame))
    (hrest : ∀ c ∈ goodSet H (commonEvent T) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius, Nonempty (RootRemainder t c)) :
    BstLean.Part243.AgentPackage 12225 H BstLean.Part243.rowRadius
      BstLean.Part249.optionBAgentFrame BstLean.Part243.rowRoot
      BstLean.Part243.proposedRetainedCharge t := by
  refine { event := commonEvent T
           measurable := commonEvent_measurable hT
           retained_charge := commonEvent_charge hcharge
           frame_bound := ?_
           root_bound := ?_ }
  · intro c hc v
    obtain ⟨F⟩ := hframe c hc
    exact BstLean.Part249.frame_from_inputs (by norm_num) F
      (sharedGood_subset (by norm_num) _ hc.2.2) v
  · intro c hc
    obtain ⟨F⟩ := hframe c hc
    obtain ⟨R⟩ := hrest c hc
    have hp : c ∈ passEvent := analyticBaseCertificate.pass_fields hc.2.1.1
    exact replacement_of_source
      (rootSource_of_events (window_of_frame F) (energy_pos_of_frame F) hp R)

end BstLean.Part252
