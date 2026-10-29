import BstLean.Part255Numeric10
import BstLean.Part255Numerics
import BstLean.Part255Selection
import BstLean.Part249Ledger
import BstLean.Part253Local

/-! Cell events, exact TI payment, and the event parameter in the covariance contract. -/
namespace BstLean.Part255
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part199 (exampleWide exampleCore example_nested OverlapGuard)
open BstLean.Part238
open BstLean.Part153 (nuA)

structure Parameters where
  wlo : ℝ
  whi : ℝ
  clo : ℝ
  chi : ℝ
  wE : ℝ
  wS : ℝ
  cE : ℝ
  cS : ℝ
  o : ℝ
  wLam : ℝ
  cLam : ℝ
  plane : ℝ
  wRadius : ℝ
  cRadius : ℝ

structure Valid (p : Parameters) : Prop where
  wlo_nonneg : 0 ≤ p.wlo
  whi_nonneg : 0 ≤ p.whi
  whi_lt : p.whi < 1
  clo_nonneg : 0 ≤ p.clo
  chi_nonneg : 0 ≤ p.chi
  chi_lt : p.chi < 1
  wE_nonneg : 0 ≤ p.wE
  wS_nonneg : 0 ≤ p.wS
  cE_nonneg : 0 ≤ p.cE
  cS_nonneg : 0 ≤ p.cS
  o_nonneg : 0 ≤ p.o
  wLam_nonneg : 0 ≤ p.wLam
  cLam_nonneg : 0 ≤ p.cLam
  wide_lam : ta_lam p.wE p.o p.wS ≤ p.wLam
  core_lam : ta_lam p.cE p.o p.cS ≤ p.cLam
  lam_order : p.cLam ≤ p.wLam
  wRadius_lt : p.wRadius < 1
  cRadius_lt : p.cRadius < 1

noncomputable def delta : ℝ := 65 * exp (-46)
noncomputable def payment : ℝ := 1 / 4000
noncomputable def sourcePayment : ℝ := 13 / 40000
noncomputable def paperCutoff : ℝ := 50 * exp (-46) / (1 / 4000)

theorem maskSlack_nonneg : 0 ≤ maskSlack := by unfold maskSlack; positivity

theorem mask_exponent : 2 * maskSlack ^ 2 * (mA 12225 : ℝ) = 46 := by
  unfold maskSlack mA
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem delta_eq :
    53 * exp (-46) + 12 * exp (-2 * maskSlack ^ 2 * (mA 12225 : ℝ)) = delta := by
  have he : -2 * maskSlack ^ 2 * (mA 12225 : ℝ) = -(46 : ℝ) := by
    nlinarith only [mask_exponent]
  rw [he]
  unfold delta
  ring

theorem source_cutoff_eq : delta / sourcePayment = paperCutoff := by
  unfold delta sourcePayment paperCutoff
  ring

theorem payment_excess : sourcePayment - payment = (3 / 40000 : ℝ) := by
  norm_num [sourcePayment, payment]

noncomputable def repairedLedger : ℝ :=
  BstLean.Part249.optionBLedger + sourcePayment - payment

theorem repaired_ledger_excess : repairedLedger - 1 / 100 =
    BstLean.Part249.optionBLedger - 1 / 100 + 3 / 40000 := by
  unfold repairedLedger
  linarith only [payment_excess]

theorem repaired_ledger_bounds :
    (10072086868 / 10 ^ 12 : ℝ) < repairedLedger ∧
      repairedLedger < (10072086869 / 10 ^ 12 : ℝ) := by
  have h := BstLean.Part249.optionB_ledger_bounds
  unfold repairedLedger sourcePayment payment
  constructor <;> linarith [h.1, h.2]

structure Supply (p : Parameters) (lo hi : ℝ) : Prop where
  valid : Valid p
  wide_num : BstLean.Part246.ta_num_sharp 12225 p.wlo p.whi p.wE p.o p.wS maskSlack 46
  core_num : BstLean.Part246.ta_num_sharp 12225 p.clo p.chi p.cE p.o p.cS maskSlack 46
  wide_guard : ∀ θ ∈ Icc lo hi, OverlapGuard 12225 θ exampleWide p.wlo p.whi
  core_guard : ∀ θ ∈ Icc lo hi, OverlapGuard 12225 θ exampleCore p.clo p.chi

noncomputable def localEvent (p : Parameters) (lo hi ε : ℝ) : Set (AgFam 12225) :=
  SharpCovEvent 12225 exampleWide exampleCore lo hi p.wLam p.cE p.o p.cS p.chi (delta / ε)

theorem localEvent_measurable (p : Parameters) (lo hi ε : ℝ) :
    MeasurableSet (localEvent p lo hi ε) :=
  measurableSet_SharpCovEvent _ _ _ _ _ _ _ _ _ _

theorem localEvent_charge {p : Parameters} {lo hi ε : ℝ}
    (S : Supply p lo hi) (hε : 0 < ε) (c : Fin 12225 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12225).real {a | ((c, τ), a) ∉ localEvent p lo hi ε} ≤ ε := by
  have hw : TI3_hyp 12225 p.wlo p.whi p.wE p.o p.wS delta := by
    rw [← delta_eq]
    exact BstLean.Part246.ta_TI3_sharp (by norm_num) S.valid.wlo_nonneg S.valid.whi_lt
      maskSlack_nonneg (by norm_num) S.wide_num
  have hc : TI3_hyp 12225 p.clo p.chi p.cE p.o p.cS delta := by
    rw [← delta_eq]
    exact BstLean.Part246.ta_TI3_sharp (by norm_num) S.valid.clo_nonneg S.valid.chi_lt
      maskSlack_nonneg (by norm_num) S.core_num
  have hw' : TI_hyp 12225 p.wlo p.whi p.wLam delta :=
    TI_hyp_mono S.valid.wide_lam le_rfl
      (BstLean.Part244.TI_hyp_of_TI3 (by norm_num) S.valid.wE_nonneg S.valid.o_nonneg
        S.valid.wS_nonneg
        (pow_lt_one₀ S.valid.whi_nonneg S.valid.whi_lt (by norm_num)) hw)
  exact SharpCovEvent_charge (by norm_num) exampleWide exampleCore example_nested
    S.valid.cE_nonneg S.valid.o_nonneg S.valid.cS_nonneg
    (pow_lt_one₀ S.valid.chi_nonneg S.valid.chi_lt (by norm_num))
    (S.valid.core_lam.trans S.valid.lam_order) (by unfold delta; positivity) hε
    S.wide_guard S.core_guard hw' hc c hτ

noncomputable def selected (p : Fin 43 → Parameters) (ε : ℝ) : Set (AgFam 12225) :=
  BstLean.Part254.selectedEvent select (fun j => localEvent (p j)
    (BstLean.Part254.cellLower (sourceIndex j)) (BstLean.Part254.cellUpper (sourceIndex j)) ε)

theorem selected_measurable (p : Fin 43 → Parameters) (ε : ℝ) :
    MeasurableSet (selected p ε) :=
  BstLean.Part254.selectedEvent_measurable select select_measurable _
    (fun _ => localEvent_measurable _ _ _ _)

theorem selected_charge (p : Fin 43 → Parameters)
    (S : ∀ j, Supply (p j) (BstLean.Part254.cellLower (sourceIndex j))
      (BstLean.Part254.cellUpper (sourceIndex j)))
    (D : Design 12225) (hτW : TauWorld D) {ε : ℝ} (hε : 0 < ε) :
    (retDist D.toCentres).real (agentEv D (selected p ε))ᶜ ≤ ε := by
  exact BstLean.Part254.selectedEvent_ret_charge D hτW select select_measurable _
    (fun _ => localEvent_measurable _ _ _ _) hε.le
    (fun c τ hτ => localEvent_charge (S _) hε c hτ)

/-- The event is explicit. In particular, a new selected event is not Option B by definition. -/
def LocalCovarianceOn (E : Set (AgFam 12225)) (cells : Fin 60 → Set ℝ)
    (caps : Fin 60 → ℝ) : Prop :=
  ∀ (i : Fin 60) (θ : ℝ), 10 ≤ i.val ∧ i.val ≤ 52 → θ ∈ cells i →
    ∀ (c : Ret 12225),
    BstLean.Part150.thetaC c.1.2 ((BstLean.Part169.paperDesignP 12225).tau0 c) = θ →
    0 < (BstLean.Part169.paperDesignP 12225).tau0 c →
    c ∈ agentEv (BstLean.Part169.paperDesignP 12225) E →
    BstLean.Part153.Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2
      ((BstLean.Part169.paperDesignP 12225).tau0 c) ≤ (13 / 10) * (2 / (12225 : ℝ)) / 12225 →
    ∀ v : Fin (mA 12225) → ℝ,
    Dq c.2.1.1.1 c.2.1.1.2 c.1.2 ((BstLean.Part169.paperDesignP 12225).tau0 c) v ≤
      caps i * (2 / (12225 : ℝ)) / 12225 * normSq v

theorem original_contract (cells : Fin 60 → Set ℝ) (caps : Fin 60 → ℝ) :
    LocalCovarianceOn (BstLean.Part249.optionBSharp 12225) cells caps ↔
      BstLean.Part253.LocalCovariance cells caps := Iff.rfl

theorem contract_of_event_inclusion {E : Set (AgFam 12225)}
    {cells : Fin 60 → Set ℝ} {caps : Fin 60 → ℝ}
    (h : BstLean.Part249.optionBSharp 12225 ⊆ E)
    (C : LocalCovarianceOn E cells caps) : BstLean.Part253.LocalCovariance cells caps := by
  intro i θ hn hi c he hτ hC hX v
  exact C i θ hn hi c he hτ (fun ht => h (hC ht)) hX v

end BstLean.Part255
