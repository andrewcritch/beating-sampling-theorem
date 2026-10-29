import BstLean.Part281Repair
import BstLean.Part281SharpSource
import BstLean.Part277Frame
namespace BstLean.Part281
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part188 BstLean.Part211
open BstLean.Part255 (sourceIndex)
open BstLean.Part281.TI (parameters parameters_valid)
open BstLean.Part263 BstLean.Part277

noncomputable def covarianceInputs_from_supplies {n : ℕ} (hn : 11883 ≤ n)
    {R : ScalarRow n} (A : FrameRepair n R)
    (S : ∀ j, Supply n (parameters j) (cellLower R.grid (sourceIndex j))
      (cellUpper R.grid (sourceIndex j)))
    (hR : ∀ j θ, θ ∈ cell R.grid (sourceIndex j) →
      BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
      BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius) :
    CovarianceInputsP (528 / 1000) n R.grid parameters (caps A) where
  supplies := S
  world_window := grid_world_windowP R (BstLean.Part277.world_upper_11883 hn) (by norm_num)
  wide_radius := fun j θ hθ => (hR j θ hθ).1
  core_radius := fun j θ hθ => (hR j θ hθ).2
  scalar := fun i θ hθ => selected_envelope hn A i hθ

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

noncomputable def frameData_from_paid_numerics {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n)
    (hu : n ≤ 16384) {wp : BstLean.Part192.WorldParameters}
    (W : BstLean.Part192.WorldPackage (BstLean.Part192.paperProgram n) wp)
    (hidden_eq : W.hidden = BstLean.Part227.hidden n (44945/10^6) (4/10000) (712/10000)
      (178/10^8) (1232/10^7))
    (lower : (202225/100000 : ℝ) ≤ BstLean.Part227.productLower n (1232/10^7))
    (upper : BstLean.Part227.productUpper n (1232/10^7) ≤ (202831/100000 : ℝ))
    {a dlo dhi k k3 MP e0 : ℝ}
    (hup : BstLean.Part227.noiseUpper n (202831 / 100000) ≤ a) (ha : a ≤ 528 / 1000)
    (hdhi : a ≤ dhi) (hdlo : dlo ≤ 0.47199)
    (E : Set (Ret n)) (hE : MeasurableSet E)
    (hpaid : E ⊆ BstLean.Part262.paidSourceBase n)
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
  baseEvent := E
  base_measurable := hE
  frameAllowance := allowance
  frame := by
    intro hW c hc
    have hθ := paid_world_window (by omega : 4096 ≤ n) W hidden_eq lower
      upper hc.1.1 (hpaid hc.2.1)
    obtain ⟨i,hi,hm⟩ := BstLean.Part263.scalarRow_world_cover R hθ
    have F := frameInputs_from_numeric_sourcesP (n := n) (R := R) (c := c) (i := i)
      h8 hn hu A C hi hm (N i hi) (direction_from_exact_windowP hup hdhi hdlo hθ)
      (paid_events_from_window (by omega) W hc.1.1 (hpaid hc.2.1) hup (ha.trans (by norm_num)) hθ)
    rw [hallowance] at F
    exact ⟨F⟩

end BstLean.Part281
