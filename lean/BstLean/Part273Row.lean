import BstLean.Part259Family
import BstLean.Part273Moment

/-! Part 273: RowInputs v2 (`RowInputsK n k`).
The noise cells are indexed by `Fin k`. The dimension floor is `8000 ≤ n`, not `11883 ≤ n`.
The ledger fields are the same as in `Part259.RowInputs`: the covariance event pays
`1/4000`, the moment event pays at most `5e-5` (Part273 base 8000), and the row pays
`baseCharge + 3 / 10000 ≤ charge ≤ retainedCharge`.
The needed cells are a predicate `needed : Fin k → Prop`; for `k = 60` it is `10 ≤ i ≤ 52`. -/
namespace BstLean.Part273
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part188
open BstLean.Part199 BstLean.Part161 BstLean.Part182
open BstLean.Part169 (paperDesignP)
open BstLean.Part192 BstLean.Part196 BstLean.Part156
open BstLean.Part249
open BstLean.Part259 (covarianceGood covarianceGood_measurable)

/-- The covariance contract on `k` cells. Only the needed cells carry the contract. -/
def LocalCovarianceOnK {n k : ℕ} (E : Set (AgFam n)) (needed : Fin k → Prop)
    (cells : Fin k → Set ℝ) (caps : Fin k → ℝ) : Prop :=
  ∀ (i : Fin k) (θ : ℝ), needed i → θ ∈ cells i →
    ∀ (c : Ret n),
    BstLean.Part150.thetaC c.1.2 ((BstLean.Part169.paperDesignP n).tau0 c) = θ →
    0 < (BstLean.Part169.paperDesignP n).tau0 c →
    c ∈ agentEv (BstLean.Part169.paperDesignP n) E →
    BstLean.Part153.Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2
      ((BstLean.Part169.paperDesignP n).tau0 c) ≤ (13 / 10) * (2 / (n : ℝ)) / n →
    ∀ v : Fin (mA n) → ℝ,
    Dq c.2.1.1.1 c.2.1.1.2 c.1.2 ((BstLean.Part169.paperDesignP n).tau0 c) v ≤
      caps i * (2 / (n : ℝ)) / n * normSq v

/-- The moment event and the covariance event cost `.0003` in total from 8000. -/
theorem covarianceGood_charge_8000 {n : ℕ} (hn : 8000 ≤ n) {event : Set (AgFam n)}
    (hpayment : (retDist (paperCentres n)).real
      (agentEv (paperDesignP n) event)ᶜ ≤ (1 / 4000 : ℝ)) :
    (retDist (paperCentres n)).real (covarianceGood event)ᶜ ≤ (3 / 10000 : ℝ) := by
  unfold covarianceGood
  rw [compl_inter]
  exact (measureReal_union_le _ _).trans
    ((add_le_add hpayment (moment_M12_ret_8000 hn
      (paperDesignP n) (paperDesign_tauWorld _ _ _ _))).trans (by norm_num))

/-- Local frame inputs on `k` cells. The cell-indexed allowances of Part259 enter here as
the values at the chosen cell. -/
structure LocalFrameInputsK (n k : ℕ) (event : Set (AgFam n)) (needed : Fin k → Prop)
    (cell : Fin k → Set ℝ) (capTable : Fin k → ℝ) (c : Ret n) (cf : ℝ) where
  cov_le : LocalCovarianceOnK event needed cell capTable
  index : Fin k
  index_needed : needed index
  member : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ cell index
  cutoff : ℝ
  centreAllowance : ℝ
  massAllowance : ℝ
  M : ℝ
  H : ℝ
  xiP : ℝ
  E : ℝ
  u : ℝ
  order : ℕ
  order_pos : 1 ≤ order
  order_le : order ≤ 12
  scale_pos : 0 < (paperDesignP n).tau0 c
  centre_pos : 0 < normSq ((paperDesignP n).bA c.1 c.2.1.1)
  centre_nonneg : ∀ j, 0 ≤ (paperDesignP n).bA c.1 c.2.1.1 j
  interfaces : WFInterfaces (paperDesignP n) c M H xiP
  centre_energy : centreEnergy (paperDesignP n) c ≤ E
  u_pos : 0 < u
  u_lt : u < 1
  cutoff_pos : 0 < cutoff
  cutoff_lt : cutoff < (1 - u) ^ 2
  gap_pos : 0 < √((1 - u) ^ 2 - cutoff) - (√E + √(xiP / n))
  covariance_nonneg : 0 ≤ capTable index
  full_centre : CENTRE_at (paperDesignP n) c centreAllowance
  mass_scalar : BstLean.Part222.massBoundOrder n order M H xiP E u cutoff ≤ massAllowance
  frame_scalar : (capTable index + centreAllowance) / cutoff + massAllowance ≤ cf

theorem covariance_from_contractK {n k : ℕ} (hn : 6 ≤ n) {event : Set (AgFam n)}
    {needed : Fin k → Prop} {cell : Fin k → Set ℝ} {capTable : Fin k → ℝ}
    (C : LocalCovarianceOnK event needed cell capTable) {c : Ret n} {i : Fin k}
    (hneeded : needed i)
    (hτ : 0 < (paperDesignP n).tau0 c)
    (hi : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ cell i)
    (hc : c ∈ covarianceGood event) :
    COV_at (paperDesignP n) c (capTable i) :=
  BstLean.Part199.cov_of_scalar hn (paperDesignP n) c hτ le_rfl
    (C i _ hneeded hi c rfl hτ hc.1 (hc.2 hτ))

theorem frame_from_inputsK {n k : ℕ} (hn : 50 ≤ n) {event : Set (AgFam n)}
    {needed : Fin k → Prop} {cell : Fin k → Set ℝ} {capTable : Fin k → ℝ}
    {c : Ret n} {cf : ℝ} (F : LocalFrameInputsK n k event needed cell capTable c cf)
    (hc : c ∈ covarianceGood event) :
    ∀ v : Fin (mA n) → ℝ,
      ∫ ξ, (∑ j, BstLean.Part134.eDir ((paperDesignP n).bA c.1 c.2.1.1)
        (hStand (paperDesignP n) c ξ) j * v j) ^ 2 ∂BstLean.Part29.stdGauss (Fin n) ≤
      cf / n * ∑ j, v j ^ 2 :=
  BstLean.Part222.freeAllowance_frame_order hn F.order_pos F.order_le
    (paperDesignP n) c F.scale_pos F.centre_pos F.centre_nonneg F.interfaces
    F.centre_energy F.u_pos F.u_lt F.cutoff_pos F.cutoff_lt F.gap_pos F.covariance_nonneg
    (covariance_from_contractK (by omega) F.cov_le F.index_needed F.scale_pos F.member hc)
    F.full_centre F.mass_scalar F.frame_scalar

/-- **RowInputs v2.** -/
structure RowInputsK (n k : ℕ) where
  dimension : 8000 ≤ n
  worldParameters : WorldParameters
  agentParameters : AgentParameters
  world : WorldPackage (paperProgram n) worldParameters
  certificate : MasterCertificate n worldParameters agentParameters
  covarianceEvent : Set (AgFam n)
  needed : Fin k → Prop
  cell : Fin k → Set ℝ
  caps : Fin k → ℝ
  covariance_measurable : MeasurableSet covarianceEvent
  covariance_payment : (retDist (paperCentres n)).real
    (agentEv (paperDesignP n) covarianceEvent)ᶜ ≤ (1 / 4000 : ℝ)
  baseEvent : Set (Ret n)
  base_measurable : MeasurableSet baseEvent
  baseCharge : ℝ
  base_payment : (retDist (paperCentres n)).real
    (BstLean.Part159.Hof world.hidden ∩ baseEventᶜ) ≤ baseCharge
  frame : ∀ c ∈ goodSet (BstLean.Part159.Hof world.hidden)
    (baseEvent ∩ covarianceGood covarianceEvent) (HbarW (paperDesignP n))
    certificate.worldRadius,
    Nonempty (LocalFrameInputsK n k covarianceEvent needed cell caps c agentParameters.frame)
  root : ∀ (t : ℝ) c, c ∈ goodSet (BstLean.Part159.Hof world.hidden)
    (baseEvent ∩ covarianceGood covarianceEvent) (HbarW (paperDesignP n))
    certificate.worldRadius →
    Nonempty (BstLean.Part243.RootInputs n t c agentParameters.root)
  payment : baseCharge + 3 / 10000 ≤ agentParameters.charge
  charge_compatible : agentParameters.charge ≤ certificate.retainedCharge

/-- The agent package from `k`-cell inputs, from dimension 8000. -/
noncomputable def agentPackageK {n k : ℕ} (hn : 8000 ≤ n) {event : Set (AgFam n)}
    {needed : Fin k → Prop} {cell : Fin k → Set ℝ} {capTable : Fin k → ℝ}
    {H E : Set (Ret n)} (hevent : MeasurableSet event)
    (hpayment : (retDist (paperCentres n)).real
      (agentEv (paperDesignP n) event)ᶜ ≤ (1 / 4000 : ℝ))
    (hE : MeasurableSet E)
    {radius frame root charge t : ℝ}
    (hcharge : (retDist (paperCentres n)).real (H ∩ Eᶜ) ≤ charge)
    (hframe : ∀ c ∈ goodSet H (E ∩ covarianceGood event)
      (HbarW (paperDesignP n)) radius,
      Nonempty (LocalFrameInputsK n k event needed cell capTable c frame))
    (hroot : ∀ c ∈ goodSet H (E ∩ covarianceGood event)
      (HbarW (paperDesignP n)) radius, Nonempty (BstLean.Part243.RootInputs n t c root)) :
    BstLean.Part243.AgentPackage n H radius frame root (charge + 3 / 10000) t := by
  have hTI := covarianceGood_charge_8000 hn hpayment
  refine { event := E ∩ covarianceGood event
           measurable := hE.inter (covarianceGood_measurable hevent)
           retained_charge := ?_
           frame_bound := ?_
           root_bound := ?_ }
  · have hs : H ∩ (E ∩ covarianceGood event)ᶜ ⊆
        (H ∩ Eᶜ) ∪ (covarianceGood event)ᶜ := by
      intro c hc
      by_cases he : c ∈ E
      · exact Or.inr (fun ht => hc.2 ⟨he, ht⟩)
      · exact Or.inl ⟨hc.1, he⟩
    exact (measureReal_mono hs (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add hcharge hTI))
  · intro c hc v
    obtain ⟨F⟩ := hframe c hc
    exact frame_from_inputsK (by omega) F hc.2.2 v
  · intro c hc
    obtain ⟨R⟩ := hroot c hc
    exact (BstLean.Part241.root_new_8000 hn t c R.split R.window R.passes
      R.fluctuation).trans R.scalar

/-- **The classifier from RowInputs v2.** -/
theorem classifier_from_rowK {n k : ℕ} (R : RowInputsK n k) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t aL (10 ^ 12) x.1 x.2)} := by
  have A := agentPackageK (t := t) R.dimension R.covariance_measurable R.covariance_payment
    R.base_measurable R.base_payment R.frame (R.root t)
  have A' : BstLean.Part243.AgentPackage n (BstLean.Part159.Hof R.world.hidden)
      R.certificate.worldRadius R.agentParameters.frame R.agentParameters.root
      R.agentParameters.charge t :=
    { A with retained_charge := A.retained_charge.trans R.payment }
  exact BstLean.Part243.checked_junction (by have := R.dimension; omega) R.world t
    R.certificate A' R.charge_compatible

structure FamilyInputsK (S : Set ℕ) (k : ℕ → ℕ) where
  row : ∀ n ∈ S, RowInputsK n (k n)

theorem classifier_on_setK {S : Set ℕ} {k : ℕ → ℕ} (R : FamilyInputsK S k) :
    ∀ n ∈ S, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t aL (10 ^ 12) x.1 x.2)} := by
  intro n hn t
  exact classifier_from_rowK (R.row n hn) t

/-! ## From Part259 (60 cells, floor 11883) to RowInputs v2 -/

/-- The needed cells of Part259: `10 ≤ i ≤ 52`. -/
def needed60 (i : Fin 60) : Prop := 10 ≤ i.val ∧ i.val ≤ 52

theorem localCovariance_toK {n : ℕ} {E : Set (AgFam n)} {cells : Fin 60 → Set ℝ}
    {caps : Fin 60 → ℝ} (C : BstLean.Part259.LocalCovarianceOn E cells caps) :
    LocalCovarianceOnK E needed60 cells caps :=
  fun i θ hi hθ c hc hτ hE hX v => C i θ hi hθ c hc hτ hE hX v

noncomputable def LocalFrameInputs.toK {n : ℕ} {event : Set (AgFam n)}
    {cell : Fin 60 → Set ℝ} {capTable : Fin 60 → ℝ} {c : Ret n} {cf : ℝ}
    (F : BstLean.Part259.LocalFrameInputs n event cell capTable c cf) :
    LocalFrameInputsK n 60 event needed60 cell capTable c cf where
  cov_le := localCovariance_toK F.cov_le
  index := F.index
  index_needed := F.index_needed
  member := F.member
  cutoff := F.cutoff F.index
  centreAllowance := F.centreAllowance (BstLean.Part253.centreGroup F.index)
  massAllowance := F.massAllowance F.index
  M := F.M
  H := F.H
  xiP := F.xiP
  E := F.E
  u := F.u
  order := F.order
  order_pos := F.order_pos
  order_le := F.order_le
  scale_pos := F.scale_pos
  centre_pos := F.centre_pos
  centre_nonneg := F.centre_nonneg
  interfaces := F.interfaces
  centre_energy := F.centre_energy
  u_pos := F.u_pos
  u_lt := F.u_lt
  cutoff_pos := F.cutoff_pos
  cutoff_lt := F.cutoff_lt
  gap_pos := F.gap_pos
  covariance_nonneg := F.covariance_nonneg
  full_centre := F.full_centre
  mass_scalar := F.mass_scalar
  frame_scalar := F.frame_scalar

/-- **`RowInputs n → RowInputsK n 60`.** -/
noncomputable def RowInputs.toK {n : ℕ} (R : BstLean.Part259.RowInputs n) :
    RowInputsK n 60 where
  dimension := le_trans (by norm_num) R.dimension
  worldParameters := R.worldParameters
  agentParameters := R.agentParameters
  world := R.world
  certificate := R.certificate
  covarianceEvent := R.covarianceEvent
  needed := needed60
  cell := R.cell
  caps := R.caps
  covariance_measurable := R.covariance_measurable
  covariance_payment := R.covariance_payment
  baseEvent := R.baseEvent
  base_measurable := R.base_measurable
  baseCharge := R.baseCharge
  base_payment := R.base_payment
  frame := fun c hc => let ⟨F⟩ := R.frame c hc; ⟨LocalFrameInputs.toK F⟩
  root := R.root
  payment := R.payment
  charge_compatible := R.charge_compatible

theorem toK_classifier {n : ℕ} (R : BstLean.Part259.RowInputs n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_from_rowK (RowInputs.toK R) t

/-! ## Generic constructor from supplies, from dimension 8000 -/

/-- A cover of the retained good set by needed cells, with a per-cell frame supply,
gives the `frame` field. -/
theorem frame_of_cover {n k : ℕ} {event : Set (AgFam n)} {needed : Fin k → Prop}
    {cell : Fin k → Set ℝ} {caps : Fin k → ℝ} {G : Set (Ret n)} {cf : ℝ}
    (cover : ∀ c ∈ G, ∃ i, needed i ∧
      BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ cell i)
    (supply : ∀ c ∈ G, ∀ i, needed i →
      BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ cell i →
      Nonempty (LocalFrameInputsK n k event needed cell caps c cf)) :
    ∀ c ∈ G, Nonempty (LocalFrameInputsK n k event needed cell caps c cf) := by
  intro c hc
  obtain ⟨i, hi, hm⟩ := cover c hc
  exact supply c hc i hi hm

/-- RowInputs v2 from its supplies on an arbitrary dimension `n ≥ 8000`. -/
noncomputable def rowK_of_supplies {n k : ℕ} (hn : 8000 ≤ n)
    {w : WorldParameters} {a : AgentParameters}
    (W : WorldPackage (paperProgram n) w) (C : MasterCertificate n w a)
    (event : Set (AgFam n)) (needed : Fin k → Prop) (cell : Fin k → Set ℝ) (caps : Fin k → ℝ)
    (hmeas : MeasurableSet event)
    (hpay : (retDist (paperCentres n)).real (agentEv (paperDesignP n) event)ᶜ ≤ (1 / 4000 : ℝ))
    (base : Set (Ret n)) (hbase : MeasurableSet base) (baseCharge : ℝ)
    (hbasePay : (retDist (paperCentres n)).real
      (BstLean.Part159.Hof W.hidden ∩ baseᶜ) ≤ baseCharge)
    (frame : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden) (base ∩ covarianceGood event)
      (HbarW (paperDesignP n)) C.worldRadius,
      Nonempty (LocalFrameInputsK n k event needed cell caps c a.frame))
    (root : ∀ t c, c ∈ BstLean.Part159.Hof W.hidden → c ∈ base →
      Nonempty (BstLean.Part243.RootInputs n t c a.root))
    (payment : baseCharge + 3 / 10000 ≤ a.charge)
    (compatible : a.charge ≤ C.retainedCharge) : RowInputsK n k where
  dimension := hn
  worldParameters := w
  agentParameters := a
  world := W
  certificate := C
  covarianceEvent := event
  needed := needed
  cell := cell
  caps := caps
  covariance_measurable := hmeas
  covariance_payment := hpay
  baseEvent := base
  base_measurable := hbase
  baseCharge := baseCharge
  base_payment := hbasePay
  frame := frame
  root := fun t c hc => root t c hc.1.1 hc.2.1
  payment := payment
  charge_compatible := compatible

end BstLean.Part273
