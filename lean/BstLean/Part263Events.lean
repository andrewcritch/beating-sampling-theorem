import BstLean.Part255Events
import BstLean.Part259Local

namespace BstLean.Part263
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part199 (exampleWide exampleCore example_nested OverlapGuard)
open BstLean.Part238
open BstLean.Part153 (nuA)
open BstLean.Part255 (Parameters Valid delta payment)

noncomputable def maskSlack (n : ℕ) : ℝ := √23 / n

theorem maskSlack_nonneg (n : ℕ) : 0 ≤ maskSlack n := by
  unfold maskSlack
  positivity

theorem mask_exponent {n : ℕ} (hn : 1 ≤ n) :
    2 * maskSlack n ^ 2 * (mA n : ℝ) = 46 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold maskSlack mA
  push_cast
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  field_simp
  <;> ring

theorem delta_eq {n : ℕ} (hn : 1 ≤ n) :
    53 * exp (-46) + 12 * exp (-2 * maskSlack n ^ 2 * (mA n : ℝ)) = delta := by
  have he : -2 * maskSlack n ^ 2 * (mA n : ℝ) = -(46 : ℝ) := by
    nlinarith only [mask_exponent hn]
  rw [he]
  unfold delta
  ring

structure Supply (n : ℕ) (p : Parameters) (lo hi : ℝ) : Prop where
  valid : Valid p
  wide_num : BstLean.Part246.ta_num_sharp n p.wlo p.whi p.wE p.o p.wS (maskSlack n) 46
  core_num : BstLean.Part246.ta_num_sharp n p.clo p.chi p.cE p.o p.cS (maskSlack n) 46
  wide_guard : ∀ θ ∈ Icc lo hi, OverlapGuard n θ exampleWide p.wlo p.whi
  core_guard : ∀ θ ∈ Icc lo hi, OverlapGuard n θ exampleCore p.clo p.chi

noncomputable def localEvent (n : ℕ) (p : Parameters) (lo hi ε : ℝ) : Set (AgFam n) :=
  SharpCovEvent n exampleWide exampleCore lo hi p.wLam p.cE p.o p.cS p.chi (delta / ε)

theorem localEvent_measurable (n : ℕ) (p : Parameters) (lo hi ε : ℝ) :
    MeasurableSet (localEvent n p lo hi ε) :=
  measurableSet_SharpCovEvent _ _ _ _ _ _ _ _ _ _

theorem localEvent_charge {n : ℕ} (hn : 2 ≤ n) {p : Parameters} {lo hi ε : ℝ}
    (S : Supply n p lo hi) (hε : 0 < ε) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {a | ((c, τ), a) ∉ localEvent n p lo hi ε} ≤ ε := by
  have hw : TI3_hyp n p.wlo p.whi p.wE p.o p.wS delta := by
    rw [← delta_eq (by omega : 1 ≤ n)]
    exact BstLean.Part246.ta_TI3_sharp hn S.valid.wlo_nonneg S.valid.whi_lt
      (maskSlack_nonneg n) (by norm_num) S.wide_num
  have hc : TI3_hyp n p.clo p.chi p.cE p.o p.cS delta := by
    rw [← delta_eq (by omega : 1 ≤ n)]
    exact BstLean.Part246.ta_TI3_sharp hn S.valid.clo_nonneg S.valid.chi_lt
      (maskSlack_nonneg n) (by norm_num) S.core_num
  have hw' : TI_hyp n p.wlo p.whi p.wLam delta :=
    TI_hyp_mono S.valid.wide_lam le_rfl
      (BstLean.Part244.TI_hyp_of_TI3 (by omega) S.valid.wE_nonneg S.valid.o_nonneg
        S.valid.wS_nonneg
        (pow_lt_one₀ S.valid.whi_nonneg S.valid.whi_lt (by norm_num)) hw)
  exact SharpCovEvent_charge (by omega) exampleWide exampleCore example_nested
    S.valid.cE_nonneg S.valid.o_nonneg S.valid.cS_nonneg
    (pow_lt_one₀ S.valid.chi_nonneg S.valid.chi_lt (by norm_num))
    (S.valid.core_lam.trans S.valid.lam_order) (by unfold delta; positivity) hε
    S.wide_guard S.core_guard hw' hc c hτ

noncomputable def selected {n N : ℕ} (σ : ℝ → Fin N)
    (p : Fin N → Parameters) (lo hi : Fin N → ℝ) (ε : ℝ) : Set (AgFam n) :=
  BstLean.Part254.selectedEvent σ (fun j => localEvent n (p j) (lo j) (hi j) ε)

theorem selected_measurable {n N : ℕ} (σ : ℝ → Fin N)
    (hσ : ∀ j, MeasurableSet {θ | σ θ = j})
    (p : Fin N → Parameters) (lo hi : Fin N → ℝ) (ε : ℝ) :
    MeasurableSet (selected (n := n) σ p lo hi ε) :=
  BstLean.Part254.selectedEvent_measurable σ hσ _
    (fun _ => localEvent_measurable _ _ _ _ _)

theorem selected_charge {n N : ℕ} (hn : 2 ≤ n) (σ : ℝ → Fin N)
    (hσ : ∀ j, MeasurableSet {θ | σ θ = j})
    (p : Fin N → Parameters) (lo hi : Fin N → ℝ)
    (S : ∀ j, Supply n (p j) (lo j) (hi j))
    (D : Design n) (hτW : TauWorld D) {ε : ℝ} (hε : 0 < ε) :
    (retDist D.toCentres).real (agentEv D (selected σ p lo hi ε))ᶜ ≤ ε := by
  exact BstLean.Part254.selectedEvent_ret_charge D hτW σ hσ _
    (fun _ => localEvent_measurable _ _ _ _ _) hε.le
    (fun c τ hτ => localEvent_charge hn (S _) hε c hτ)

theorem selected_payment {n N : ℕ} (hn : 2 ≤ n) (σ : ℝ → Fin N)
    (hσ : ∀ j, MeasurableSet {θ | σ θ = j})
    (p : Fin N → Parameters) (lo hi : Fin N → ℝ)
    (S : ∀ j, Supply n (p j) (lo j) (hi j)) :
    (retDist (BstLean.Part169.paperDesignP n).toCentres).real
      (agentEv (BstLean.Part169.paperDesignP n) (selected σ p lo hi payment))ᶜ ≤
        (1 / 4000 : ℝ) :=
  selected_charge hn σ hσ p lo hi S _ (paperDesign_tauWorld _ _ _ _)
    (by norm_num [payment])

end BstLean.Part263
