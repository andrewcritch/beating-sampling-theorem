import BstLean.Part275Interface

/-! Part 280, the root interface with a general table event.

`ActualRootCertificateP` (Part 275) fixes the table event to `tableEventP n a b`.
The sharp table events of Parts 276 and 280 have a different guard, so this file
states the same certificate with any measurable table event `T` and a row guard `G`.
The row guard is a property of the retained value that the row supplies (for M2:
the World angle bound `θ ≤ θmax`). -/
namespace BstLean.Part280
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part188 BstLean.Part195 BstLean.Part222
open BstLean.Part275

/-- The source base with a general table event: the paid source base of Part 262
(analytic base, positive output, `Operator160`) intersected with `T`. -/
def sharpSourceBase (n : ℕ) (T : Set (Ret n)) : Set (Ret n) :=
  BstLean.Part262.paidSourceBase n ∩ T

theorem sharpSourceBase_measurable {n : ℕ} (hn : 1 ≤ n) {T : Set (Ret n)}
    (hT : MeasurableSet T) : MeasurableSet (sharpSourceBase n T) := by
  have hp : MeasurableSet (BstLean.Part262.paidSourceBase n) := by
    unfold BstLean.Part262.paidSourceBase
    exact ((BstLean.Part262.analyticBase_measurable hn).inter
      (BstLean.Part252.positiveOutputEvent_measurable _)).inter
      (BstLean.Part160.measurableSet_agentEv _ (BstLean.Part252.measurableSet_Operator160 _))
  exact hp.inter hT

theorem sharpSourceBase_charge {n : ℕ} (hn : 8000 ≤ n) {T : Set (Ret n)} {tb : ℝ}
    (hT : (retDist (paperCentres n)).real Tᶜ ≤ tb) (H : Set (Ret n)) :
    (retDist (paperCentres n)).real (H ∩ (sharpSourceBase n T)ᶜ) ≤ sourceChargeFn n + tb := by
  have hs : H ∩ (sharpSourceBase n T)ᶜ ⊆
      (H ∩ (BstLean.Part262.paidSourceBase n)ᶜ) ∪ Tᶜ := by
    intro c hc
    by_cases hp : c ∈ BstLean.Part262.paidSourceBase n
    · exact Or.inr (fun ht => hc.2 ⟨hp, ht⟩)
    · exact Or.inl ⟨hc.1, hp⟩
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (paidSourceBase_charge_8000 hn H) hT))

/-- The successor of `ActualRootCertificateP` with a general table event `T` and a
row guard `G`. The caps fields `tableF` and `tableW` are not used. -/
structure SharpRootCertificate (n : ℕ) (root : ℝ) (caps : RootCaps)
    (T : Set (Ret n)) (G : Ret n → Prop) where
  dimension : 8000 ≤ n
  table_measurable : MeasurableSet T
  source_charge : sourceChargeFn n ≤ caps.sourceCharge
  table_payment : (retDist (paperCentres n)).real Tᶜ ≤ caps.tableCharge
  inputs : ∀ (t : ℝ) (c : Ret n), WINDOW (paperDesignP n) c → G c →
    c ∈ sharpSourceBase n T →
    WFInterfaces (paperDesignP n) c caps.Mcap (caps.Hcap n) caps.xiCap →
    centreEnergy (paperDesignP n) c ≤ caps.Ecap →
    BstLean.Part243.RootInputs n t c root

/-- The local supplies on a set `H` of retained values. -/
structure SharpLocalSupply (n : ℕ) (caps : RootCaps) (T : Set (Ret n))
    (G : Ret n → Prop) (H : Set (Ret n)) : Prop where
  window : ∀ c ∈ H, c ∈ sharpSourceBase n T → WINDOW (paperDesignP n) c
  guard : ∀ c ∈ H, c ∈ sharpSourceBase n T → G c
  interfaces : ∀ c ∈ H, c ∈ sharpSourceBase n T →
    WFInterfaces (paperDesignP n) c caps.Mcap (caps.Hcap n) caps.xiCap
  energy_cap : ∀ c ∈ H, c ∈ sharpSourceBase n T →
    centreEnergy (paperDesignP n) c ≤ caps.Ecap

theorem payment_of_sharp {n : ℕ} {root : ℝ} {caps : RootCaps} {T : Set (Ret n)}
    {G : Ret n → Prop} (C : SharpRootCertificate n root caps T G) (H : Set (Ret n)) :
    (retDist (paperCentres n)).real (H ∩ (sharpSourceBase n T)ᶜ) ≤
      caps.sourceCharge + caps.tableCharge :=
  (sharpSourceBase_charge C.dimension C.table_payment H).trans
    (by linarith [C.source_charge])

/-- The adapter to the Part 262 base root supply that the row routes consume. -/
noncomputable def sharpBaseRootSupply {n : ℕ} {root : ℝ} {caps : RootCaps}
    {T : Set (Ret n)} {G : Ret n → Prop} (C : SharpRootCertificate n root caps T G)
    (H : Set (Ret n)) (L : SharpLocalSupply n caps T G H) :
    BstLean.Part262.BaseRootSupply n H root (caps.sourceCharge + caps.tableCharge) where
  event := sharpSourceBase n T
  measurable := sharpSourceBase_measurable (by have := C.dimension; omega) C.table_measurable
  payment := payment_of_sharp C H
  inputs := fun t c hw hc => C.inputs t c (L.window c hw hc) (L.guard c hw hc) hc
    (L.interfaces c hw hc) (L.energy_cap c hw hc)

/-- The common event with the covariance event (RowInputs v2 ledger, +3/10000). -/
def sharpCommonEvent (n : ℕ) (T : Set (Ret n))
    (covarianceEvent : Set (BstLean.Part160.AgFam n)) : Set (Ret n) :=
  sharpSourceBase n T ∩ BstLean.Part259.covarianceGood covarianceEvent

theorem sharp_common_payment {n : ℕ} {root : ℝ} {caps : RootCaps} {T : Set (Ret n)}
    {G : Ret n → Prop} (C : SharpRootCertificate n root caps T G)
    {event : Set (BstLean.Part160.AgFam n)}
    (hCovariance : (retDist (paperCentres n)).real
      (BstLean.Part160.agentEv (paperDesignP n) event)ᶜ ≤ (1 / 4000 : ℝ))
    (H : Set (Ret n)) :
    (retDist (paperCentres n)).real (H ∩ (sharpCommonEvent n T event)ᶜ) ≤
      caps.sourceCharge + caps.tableCharge + 3 / 10000 := by
  have hs : H ∩ (sharpCommonEvent n T event)ᶜ ⊆
      (H ∩ (sharpSourceBase n T)ᶜ) ∪ (BstLean.Part259.covarianceGood event)ᶜ := by
    intro c hc
    by_cases hb : c ∈ sharpSourceBase n T
    · exact Or.inr (fun hg => hc.2 ⟨hb, hg⟩)
    · exact Or.inl ⟨hc.1, hb⟩
  have hp := BstLean.Part273.covarianceGood_charge_8000 C.dimension hCovariance
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (payment_of_sharp C H) hp))

/-- The local frame inputs of RowInputs v2 give the remaining local interfaces. -/
noncomputable def sharpRootInputs_from_frameK {n k : ℕ} {root t cf : ℝ} {caps : RootCaps}
    {T : Set (Ret n)} {G : Ret n → Prop}
    {event : Set (BstLean.Part160.AgFam n)} {needed : Fin k → Prop}
    {cell : Fin k → Set ℝ} {capTable : Fin k → ℝ}
    {c : Ret n} (C : SharpRootCertificate n root caps T G)
    (F : BstLean.Part273.LocalFrameInputsK n k event needed cell capTable c cf)
    (hc : c ∈ sharpSourceBase n T) (hG : G c)
    (hcell : cell F.index ⊆ Icc (46 / 100 : ℝ) (54 / 100))
    (hM : F.M ≤ caps.Mcap) (hH : F.H ≤ caps.Hcap n)
    (hxi : F.xiP ≤ caps.xiCap) (hE : F.E ≤ caps.Ecap) :
    BstLean.Part243.RootInputs n t c root := by
  have hn : 1 ≤ n := by have := C.dimension; omega
  have hw := BstLean.Part252.window_of_theta hn (paperDesignP n) c
    F.scale_pos (hcell F.member)
  have I : WFInterfaces (paperDesignP n) c caps.Mcap (caps.Hcap n) caps.xiCap := by
    refine ⟨BstLean.Part219.directionMoment_mono F.interfaces.direction hM, ?_, ?_⟩
    · exact ⟨F.interfaces.energy.1.trans hH, F.interfaces.energy.2.1,
        F.interfaces.energy.2.2.trans (pow_le_pow_left₀ F.interfaces.energy.1 hH 32)⟩
    · refine ⟨F.interfaces.parallel.1.trans hxi, F.interfaces.parallel.2.trans ?_⟩
      apply sqrt_le_sqrt
      exact div_le_div_of_nonneg_right hxi (Nat.cast_nonneg n)
  exact C.inputs t c hw hG hc I (F.centre_energy.trans hE)

/-! ### M2 caps -/

/-- The source charge on M2: at most .000601 from 11883 (Part 262: .000599145 from 12224). -/
theorem sourceChargeFn_le_m2 {n : ℕ} (hn : 11883 ≤ n) : sourceChargeFn n ≤ 601 / 10 ^ 6 :=
  (sourceChargeFn_anti (n0 := 11883) (by norm_num) hn).trans
    (by unfold sourceChargeFn centreCharge; norm_num)

/-- The low-mass guards on M2 at base 11883: direction cap .0912, `u = .0042`, the M2 cutoff
`d = .215240`, budget `4e-12` and gap `g = .0414` (the pilot gap .04 fails below about
12000). -/
theorem lowMass_m2_11883 :
    LowMassNumerics 11883 (912 / 10000) ((2101 / 100) / (11883 : ℕ)) (4 / 100) (702 / 1000)
      (42 / 10000) (215240 / 10 ^ 6) (4 / 10 ^ 12) (414 / 10000) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · have h1 : (881122 / 10 ^ 6 : ℝ) ≤ √((1 - 42 / 10000) ^ 2 - 215240 / 10 ^ 6) :=
      le_sqrt_of_sq_le (by norm_num)
    have h2 : √(702 / 1000 : ℝ) ≤ 837855 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
    have h3 : √((4 / 100 : ℝ) / (11883 : ℕ)) ≤ 1835 / 10 ^ 6 :=
      sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    linarith
  · unfold lowMassPrice
    norm_num

theorem lowMass_m2 {n : ℕ} (hn : 11883 ≤ n) :
    LowMassNumerics n (912 / 10000) ((2101 / 100) / n) (4 / 100) (702 / 1000)
      (42 / 10000) (215240 / 10 ^ 6) (4 / 10 ^ 12) (414 / 10000) :=
  lowMassNumerics_base (n0 := 11883) (by norm_num) hn (by norm_num) (by norm_num)
    (by norm_num) lowMass_m2_11883

end BstLean.Part280
