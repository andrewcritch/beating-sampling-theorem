import BstLean.Part264Repair
import BstLean.Part264Source

/-! Actual covariance and local source supplies consume the repaired scalar rows. -/
namespace BstLean.Part264
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263

noncomputable def frameInputs_from_repair {n : ℕ} (hn : 11883 ≤ n)
    {R : ScalarRow n} (A : FrameRepair n R)
    (C : CovarianceInputs n R.grid parameters (caps A))
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
  exact frameInputs_from_network (localCov hn C) hi hm S N' rfl le_rfl

noncomputable def frameInputs_from_numeric_sources {n : ℕ} (hn : n ∈ Icc 12225 12349)
    {R : ScalarRow n} (A : FrameRepair n R)
    (C : CovarianceInputs n R.grid parameters (caps A))
    {c : Ret n} {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ cell R.grid i)
    (N : CellSourceNumerics n (R.table i) R.M R.H R.xi)
    (hw : c ∈ BstLean.Part159.Hof (BstLean.Part260.worldPackage n hn).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase n) :
    BstLean.Part259.LocalFrameInputs n (covarianceEvent n R.grid parameters)
      (cell R.grid) (caps A) c R.targetFrame :=
  frameInputs_from_repair (by have := hn.1; omega) A C hi hm
    (network_from_numerics hn N (scalarRow_cell_subset R i hm) hw hc)

end BstLean.Part264
