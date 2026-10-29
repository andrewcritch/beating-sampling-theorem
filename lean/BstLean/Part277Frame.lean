import BstLean.Part277Cov
import BstLean.Part277Window
import BstLean.Part277Moment
import BstLean.Part264Frame
import BstLean.Part264Covariance
import BstLean.Part269WorldSource

/-! Part 277, frame: the frame chain of `Part264Repair`, `Part264Covariance`, `Part264Frame`,
`Part269RepairCommon`, `Part269Source`, `Part269WorldSource` and `Part269FrameAdapter` on a base
`n0 ≥ 8000`.
Changes against the old chain:
* the dimension floors `11883`, `12225` become `8000 ≤ n0 ≤ n`;
* the direction window `[0.47199, 0.52358]` becomes `[dlo, dhi]`;
* the lower energy `0.665`, the operator cap `1.22`, the pair `(1.22, 1.12)` become parameters
  `e0`, `MP`, `(k, k3)` of `CellSourceNumericsP`;
* the covariance contract is `CovarianceInputsP` with window top `.528`. -/
namespace BstLean.Part277
open Real Set MeasureTheory
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part188 BstLean.Part211
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263
open BstLean.Part264 (FrameRepair caps repairedCell repair_certificate caps_source
  select_le_of_mem)

/-! ## Envelope and repair (Part264Repair, Part269RepairCommon) -/

theorem envelope_dimension_leP {a n : ℕ} (ha : 8000 ≤ a) (han : a ≤ n)
    (p : BstLean.Part255.Parameters) (hp : BstLean.Part255.Valid p) {θ : ℝ} (hθ : 0 ≤ θ)
    (hhi : θ ≤ 528 / 1000) : envelope n p θ ≤ envelope a p θ := by
  have haR : (8000 : ℝ) ≤ a := by exact_mod_cast ha
  have hanR : (a : ℝ) ≤ n := by exact_mod_cast han
  have ha0 : (0 : ℝ) < a := by linarith
  have hd : 0 < 1 - 4 * θ / a := by
    have h := (div_lt_one ha0).mpr (by linarith : 4 * θ < (a : ℝ))
    linarith
  have hdiv : 4 * θ / (n : ℝ) ≤ 4 * θ / a :=
    div_le_div_of_nonneg_left (by positivity) ha0 hanR
  have hterm := div_le_div_of_nonneg_left hp.cLam_nonneg hd
    (show 1 - 4 * θ / a ≤ 1 - 4 * θ / n by linarith)
  unfold BstLean.Part263.envelope
  exact add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hterm le_rfl) le_rfl) hθ) le_rfl

theorem envelope_on_cellP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {R : ScalarRow n}
    (F : FrameRepair n R) (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex j)) :
    envelope n (parameters j) θ ≤ F.cap j := by
  have hs := scalarRow_cell_subset R (sourceIndex j) hθ
  have hθ0 : 0 ≤ θ := by
    have h := (cell_source hθ).1
    have hg := R.grid.top_pos.le
    unfold noiseNode at h
    have hz : 0 ≤ (R.grid.top - 46 / 100) * (sourceIndex j).val / 60 := by positivity
    linarith
  exact (envelope_monoP h8 hn _ (parameters_valid j) hθ0 hs.2
    ((F.endpoint_upper j).trans (by norm_num))
    (parameters_valid j).wRadius_lt (parameters_valid j).cRadius_lt).trans (F.endpoint j)

theorem selected_envelopeP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {R : ScalarRow n}
    (F : FrameRepair n R) (i : Fin 60) {θ : ℝ} (hθ : θ ∈ cell R.grid i) :
    envelope n (parameters (select R.grid.top θ)) θ ≤ caps F i := by
  have hw := cell_world hθ
  have hs := envelope_on_cellP h8 hn F (select R.grid.top θ) (select_member R.grid hw)
  have hi := cell_needed hθ
  rw [BstLean.Part264.caps, dif_pos hi]
  exact hs.trans (F.cap_mono (select_le_of_mem hθ))

/-! ## Covariance inputs (Part264Covariance) -/

theorem grid_world_windowP {n : ℕ} (R : ScalarRow n) {a : ℝ}
    (hup : BstLean.Part227.noiseUpper n (202831 / 100000) ≤ a) (ha : a ≤ 528 / 1000) :
    Icc R.grid.worldLower R.grid.worldUpper ⊆ Icc (46 / 100 : ℝ) (528 / 1000) := by
  intro θ hθ
  rw [R.grid_lower, R.grid_upper] at hθ
  exact ⟨(le_trans (by norm_num) BstLean.Part250.noiselo.1).trans hθ.1,
    hθ.2.trans (hup.trans ha)⟩

noncomputable def covarianceInputs_from_suppliesP {n : ℕ} {R : ScalarRow n} {a : ℝ}
    (hup : BstLean.Part227.noiseUpper n (202831 / 100000) ≤ a) (ha : a ≤ 528 / 1000)
    {n0 : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) (A : FrameRepair n R)
    (S : ∀ j, Supply n (parameters j) (cellLower R.grid (sourceIndex j))
      (cellUpper R.grid (sourceIndex j)))
    (hR : ∀ j θ, θ ∈ cell R.grid (sourceIndex j) →
      BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
      BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius) :
    CovarianceInputsP (528 / 1000) n R.grid parameters (caps A) where
  supplies := S
  world_window := grid_world_windowP R hup ha
  wide_radius := fun j θ hθ => (hR j θ hθ).1
  core_radius := fun j θ hθ => (hR j θ hθ).2
  scalar := fun i θ hθ => selected_envelopeP h8 hn A i hθ

/-! ## Frame inputs (Part264Frame) -/

noncomputable def frameInputs_from_repairP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n)
    {R : ScalarRow n} (A : FrameRepair n R)
    (C : CovarianceInputsP (528 / 1000) n R.grid parameters (caps A))
    {c : Ret n} {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ cell R.grid i)
    (N : NetworkInputs n c (R.table i) R.M R.H R.xi) :
    BstLean.Part259.LocalFrameInputs n (covarianceEvent n R.grid parameters)
      (cell R.grid) (caps A) c R.targetFrame := by
  let j : Fin 43 := ⟨i.val - 10, by omega⟩
  have he : sourceIndex j = i := by
    apply Fin.ext
    dsimp [sourceIndex, j]
    omega
  have hcap : caps A i = A.cap j := by rw [← he, caps_source]
  have hc : 0 ≤ caps A i := by rw [hcap]; exact A.cap_nonneg j
  have hf : (caps A i + (R.table i).centre) / (R.table i).cutoff + 11 / 1000 ≤
      R.targetFrame := by
    rw [hcap, ← he]
    exact A.frame j
  have S := repair_certificate (R.certificate i) hc hf
  have N' : NetworkInputs n c (repairedCell (R.table i) (caps A i) R.targetFrame)
      R.M R.H R.xi := ⟨N.scale_pos,N.centre_pos,N.interfaces,N.centre_energy,N.full_centre⟩
  exact frameInputs_from_network (localCovP h8 hn (by norm_num) C) hi hm S N' rfl le_rfl

/-! ## Cell numerics (Part269Source) -/

/-- The numerics of one cell, with the pair `(k, k3)`, the operator cap `MP`, the lower energy
`e0` and the direction window `[dlo, dhi]` as parameters. -/
structure CellSourceNumericsP (n : ℕ) (r : CellData) (M H xi k k3 MP e0 dlo dhi : ℝ) where
  thetaHi : ℝ
  S : ℝ
  certificate : CentreCertificate n n 0.011 k k3 (0.46) thetaHi S MP (1 - r.lower)
    (fun _ => 0.006)
  energy_allowance : BstLean.Part222.energyAllowance n ≤ H
  parallel_nonneg : 0 ≤ xi
  centre_nonneg : 0 ≤ r.centre
  centre_upper : r.centre ≤ 0.1
  MP_nonneg : 0 ≤ MP
  e0_pos : 0 < e0
  operator : ∀ (c : Fin n → ℝ) {τ : ℝ}, 0 < τ →
    BstLean.Part219.operatorAllowance c τ 0.006 (ENNReal.ofReal (1 / 20000)) ^ 2 ≤ MP
  lower : ∀ θ ∈ Icc (0.46 : ℝ) thetaHi,
    e0 ≤ energyLower n (gMinus n) (gPlus n) (finiteEnergy n n 0.011) θ
  direction : ∀ (c : Fin n → ℝ) (τ e xi eta : ℝ) (δ : ℝ≥0∞),
    BstLean.Part150.thetaC c τ ∈ Icc dlo dhi →
    e0 ≤ e → 0 ≤ xi → xi ≤ 0.1 →
    BstLean.Part219.operatorAllowance c τ eta δ ^ 2 ≤ MP →
    BstLean.Part219.paperDirectionBudget c τ e xi eta δ ≤ M
  source_lower : 0.46 ≤ r.lower
  source_upper : r.upper ≤ thetaHi
  source_upper_one : r.upper ≤ 1
  full_scalar : fullFormula n n 0.011 k k3 (0.46) thetaHi S MP ≤ r.centre
  parallel_scalar : parallelFormula n n 0.011
    (momentAllowance n BstLean.Part154.csC 0.011 k k3 thetaHi S)
    (BstLean.Part154.bN n BstLean.Part154.csC thetaHi)
    (√(momentAllowance n BstLean.Part154.csC 0.011 k k3 thetaHi S) +
      sharpDeviation n BstLean.Part154.csC 0.011 (0.46) thetaHi) thetaHi MP ≤ xi
  upper_scalar : BstLean.Part206.energyUpper n (gMinus n) (gPlus n)
    (finiteEnergy n n 0.011) (1 - r.lower) ≤ r.energy

noncomputable def sourceInputs_of_numericsP {n : ℕ} {c : Ret n} {r : CellData}
    {M H xi k k3 MP e0 dlo dhi : ℝ}
    (N : CellSourceNumericsP n r M H xi k k3 MP e0 dlo dhi)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc r.lower r.upper)
    (hDir : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc dlo dhi)
    (F : BstLean.Part262.SourceEvents c) (hn : 2 ≤ n) :
    BstLean.Part263.SourceInputs n c r M H xi where
  energy_allowance := N.energy_allowance
  parallel_nonneg := N.parallel_nonneg
  J := n
  J_pos := by omega
  delta := 0.011
  k := k
  k3 := k3
  thetaLo := 0.46
  thetaHi := N.thetaHi
  S := N.S
  MP := MP
  qWorld := 1 - r.lower
  lowerEnergy := e0
  eta := 0.006
  v := fun _ => 0.006
  certificate := N.certificate
  world_centre_pos := F.world_centre_pos
  scale_pos := F.scale_pos
  centre_eq := BstLean.Part263.paper_centre_eq c
  lower_pos := N.e0_pos
  full_nonneg := N.centre_nonneg
  MP_nonneg := N.MP_nonneg
  window := ⟨N.source_lower.trans hm.1, hm.2.trans N.source_upper⟩
  world_cap := sub_le_sub_left hm.1 1
  signal_domain := by
    have hl := N.source_lower.trans hm.1
    have hu := hm.2.trans N.source_upper_one
    constructor <;> linarith
  full_scalar := N.full_scalar
  parallel_scalar := N.parallel_scalar
  lower_scalar := N.lower _ ⟨N.source_lower.trans hm.1, hm.2.trans N.source_upper⟩
  upper_scalar := N.upper_scalar
  operator_scalar := N.operator _ F.scale_pos
  direction_scalar := N.direction _ _ _ _ _ _ hDir le_rfl
    N.centre_nonneg N.centre_upper (N.operator _ F.scale_pos)
  base_event := F.base_event
  error_event := F.error_event
  operator_event := F.operator_event
  energy_event := F.energy_event

theorem network_from_numericsP {n : ℕ} (hn : 8000 ≤ n) (hu : n ≤ 16384)
    {c : Ret n} {r : CellData} {M H xi k k3 MP e0 dlo dhi : ℝ}
    (N : CellSourceNumericsP n r M H xi k k3 MP e0 dlo dhi)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc r.lower r.upper)
    (hDir : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc dlo dhi)
    (F : BstLean.Part262.SourceEvents c) : BstLean.Part263.NetworkInputs n c r M H xi :=
  BstLean.Part263.network_from_source (by omega) hu
    (sourceInputs_of_numericsP N hm hDir F (by omega))

noncomputable def frameInputs_from_numeric_sourcesP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n)
    (hu : n ≤ 16384) {R : ScalarRow n} (A : FrameRepair n R)
    (C : CovarianceInputsP (528 / 1000) n R.grid parameters (caps A))
    {c : Ret n} {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52)
    {k k3 MP e0 dlo dhi : ℝ}
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ cell R.grid i)
    (N : CellSourceNumericsP n (R.table i) R.M R.H R.xi k k3 MP e0 dlo dhi)
    (hDir : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc dlo dhi)
    (F : BstLean.Part262.SourceEvents c) :
    BstLean.Part259.LocalFrameInputs n (covarianceEvent n R.grid parameters)
      (cell R.grid) (caps A) c R.targetFrame :=
  frameInputs_from_repairP h8 hn A C hi hm
    (network_from_numericsP (by omega) hu N (scalarRow_cell_subset R i hm) hDir F)

/-! ## World source (Part269WorldSource) -/

theorem events_from_exact_windowP {n : ℕ} (hn : 8000 ≤ n) {wp : BstLean.Part192.WorldParameters}
    (W : BstLean.Part192.WorldPackage (BstLean.Part192.paperProgram n) wp) {c : Ret n}
    (hw : c ∈ BstLean.Part159.Hof W.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase n) {a : ℝ}
    (hup : BstLean.Part227.noiseUpper n (202831 / 100000) ≤ a) (ha : a ≤ 54 / 100)
    (hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225 / 100000))
        (BstLean.Part227.noiseUpper n (202831 / 100000))) :
    BstLean.Part262.SourceEvents c := by
  have hwin := BstLean.Part252.window_of_theta (by omega : 1 ≤ n)
    (paperDesignP n) c (BstLean.Part269.world_scale_pos W hw)
    (show BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
      Icc (46/100 : ℝ) (54/100) from
      ⟨(le_trans (by norm_num) BstLean.Part250.noiselo.1).trans hθ.1,
       hθ.2.trans (hup.trans ha)⟩)
  exact BstLean.Part262.sourceEvents_of_base hwin hc

theorem direction_from_exact_windowP {n : ℕ} {θ a dlo dhi : ℝ}
    (hup : BstLean.Part227.noiseUpper n (202831 / 100000) ≤ a) (ha : a ≤ dhi)
    (hlo : dlo ≤ 0.47199)
    (hθ : θ ∈ Icc (BstLean.Part227.noiseLower (202225 / 100000))
      (BstLean.Part227.noiseUpper n (202831 / 100000))) : θ ∈ Icc dlo dhi :=
  ⟨hlo.trans ((le_trans (by norm_num) BstLean.Part250.noiselo.1).trans hθ.1),
    hθ.2.trans (hup.trans ha)⟩

/-! ## Frame data (Part269FrameAdapter) -/

noncomputable def frameData_from_numericsP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n)
    (hu : n ≤ 16384) {wp : BstLean.Part192.WorldParameters}
    (W : BstLean.Part192.WorldPackage (BstLean.Part192.paperProgram n) wp)
    (hidden_eq : W.hidden = BstLean.Part227.hidden n (44945/10^6) (4/10000) (712/10000)
      (178/10^8) (1232/10^7))
    (lower : (202225/100000 : ℝ) ≤ BstLean.Part227.productLower n (1232/10^7))
    (upper : BstLean.Part227.productUpper n (1232/10^7) ≤ (202831/100000 : ℝ))
    {a dlo dhi k k3 MP e0 : ℝ}
    (hup : BstLean.Part227.noiseUpper n (202831 / 100000) ≤ a) (ha : a ≤ 528 / 1000)
    (hdhi : a ≤ dhi) (hdlo : dlo ≤ 0.47199)
    (R : ScalarRow n) (A : FrameRepair n R)
    (C : CovarianceInputsP (528 / 1000) n R.grid parameters (caps A))
    (N : ∀ i : Fin 60, (10 ≤ i.val ∧ i.val ≤ 52) →
      CellSourceNumericsP n (R.table i) R.M R.H R.xi k k3 MP e0 dlo dhi)
    (allowance : ℝ) (hallowance : R.targetFrame = allowance) :
    BstLean.Part264b.FrameData n where
  worldParameters := wp
  world := W
  covarianceEvent := covarianceEvent n R.grid parameters
  cell := cell R.grid
  caps := caps A
  covariance_measurable := BstLean.Part263.covarianceEvent_measurable _ _ _
  covariance_payment := covarianceEvent_paymentP (by omega) C
  baseEvent := BstLean.Part262.sourceBase n
  base_measurable := BstLean.Part262.sourceBase_measurable (by omega)
  frameAllowance := allowance
  frame := by
    intro hW c hc
    have hθ := BstLean.Part269.exact_world_window (by omega : 4096 ≤ n) W hidden_eq lower
      upper hc.1.1 hc.2.1
    obtain ⟨i,hi,hm⟩ := BstLean.Part263.scalarRow_world_cover R hθ
    have F := frameInputs_from_numeric_sourcesP (n := n) (R := R) (c := c) (i := i)
      h8 hn hu A C hi hm (N i hi) (direction_from_exact_windowP hup hdhi hdlo hθ)
      (events_from_exact_windowP (by omega) W hc.1.1 hc.2.1 hup (ha.trans (by norm_num)) hθ)
    rw [hallowance] at F
    exact ⟨F⟩

end BstLean.Part277
