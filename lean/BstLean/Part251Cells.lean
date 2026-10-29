import BstLean.Part251Obstruction

/-! A finite audit of proposed noise-cell constants.
An audit proves incompatibility with Part249's fixed certificate expression.
It does not promote proposed constants to network bounds. -/
namespace BstLean.Part251
open Real Set BstLean.Part130 BstLean.Part157

/-- The upward decimal endpoint stored in the specified chain row. -/
noncomputable def proposedThetaUpper : ℝ := 531966295480402052191389 / 10 ^ 24

noncomputable def noiseNode (j : ℕ) : ℝ :=
  46 / 100 + (proposedThetaUpper - 46 / 100) * j / 60

theorem noiseNode_mono : Monotone noiseNode := by
  intro i j hij
  have h : (i : ℝ) ≤ j := by exact_mod_cast hij
  dsimp [noiseNode]
  have h0 : 0 ≤ proposedThetaUpper - 46 / 100 := by norm_num [proposedThetaUpper]
  gcongr

theorem noiseNode_zero : noiseNode 0 = (46 / 100 : ℝ) := by simp [noiseNode]

theorem noiseNode_sixty : noiseNode 60 = proposedThetaUpper := by
  norm_num [noiseNode]

theorem noise_cells_cover {θ : ℝ}
    (hθ : θ ∈ Icc (46 / 100) proposedThetaUpper) :
    ∃ i : Fin 60, θ ∈ Icc (noiseNode i.val) (noiseNode (i.val + 1)) := by
  obtain ⟨j, hj, hc⟩ := BstLean.Part193.chain_coverage noiseNode
    (by norm_num : 0 < 60) (fun j _ => noiseNode_mono (Nat.le_succ j))
    (show noiseNode 0 ≤ θ ∧ θ ≤ noiseNode 60 by
      simpa only [noiseNode_zero, noiseNode_sixty] using (show 46 / 100 ≤ θ ∧
        θ ≤ proposedThetaUpper from hθ))
  exact ⟨⟨j, Finset.mem_range.mp hj⟩, hc⟩

theorem cells_inside_window {i : Fin 60} (hi : i.val ≤ 55) {θ : ℝ}
    (hθ : θ ∈ Icc (noiseNode i.val) (noiseNode (i.val + 1))) :
    θ ∈ Icc (46 / 100) (528 / 1000) := by
  have hlo := noiseNode_mono (Nat.zero_le i.val)
  have hhi := noiseNode_mono (show i.val + 1 ≤ 56 by omega)
  rw [noiseNode_zero] at hlo
  have h56 : noiseNode 56 ≤ (528 / 1000 : ℝ) := by norm_num [noiseNode, proposedThetaUpper]
  exact ⟨hlo.trans hθ.1, hθ.2.trans (hhi.trans h56)⟩

theorem cell56_crosses_window : noiseNode 56 < (528 / 1000 : ℝ) ∧
    (528 / 1000 : ℝ) < noiseNode 57 := by
  norm_num [noiseNode, proposedThetaUpper]

theorem cells_outside_window {i : Fin 60} (hi : 57 ≤ i.val) {θ : ℝ}
    (hθ : θ ∈ Icc (noiseNode i.val) (noiseNode (i.val + 1))) :
    (528 / 1000 : ℝ) < θ :=
  cell56_crosses_window.2.trans_le ((noiseNode_mono hi).trans hθ.1)

structure CellAudit (i : Fin 60) where
  covarianceCap : ℝ
  centreCap : ℝ
  covariance_nonneg : 0 ≤ covarianceCap
  covariance_too_small : covarianceCap < (598 / 1000 : ℝ) * noiseNode i.val
  centre_too_large : (8454 / 100000 : ℝ) ≤ centreCap

/-- No refinement of a nonempty cell can turn its proposed covariance cap into
a bound on the fixed Part249 expression within the installed noise window. -/
theorem cell_covariance_rejected {i : Fin 60} (A : CellAudit i) {θ : ℝ}
    (hw : θ ∈ Icc (46 / 100) (528 / 1000))
    (hθ : noiseNode i.val ≤ θ) : A.covarianceCap < fixedCovariance 12225 θ := by
  exact A.covariance_too_small.trans_le
    ((mul_le_mul_of_nonneg_left hθ (by norm_num)).trans
      (fixedCovariance_lower (by norm_num) hw))

theorem cell_frameInputs_rejected {i : Fin 60} (A : CellAudit i) {c : Ret 12225}
    (F : BstLean.Part249.FrameInputs 12225 c BstLean.Part249.optionBAgentFrame)
    (hc : noiseNode i.val ≤
      BstLean.Part150.thetaC c.1.2 ((BstLean.Part169.paperDesignP 12225).tau0 c))
    (hN : F.N ≤ A.covarianceCap) : False := by
  have h := cell_covariance_rejected A F.window hc
  exact (not_lt_of_ge (F.covariance_scalar.trans hN)) h

theorem cell_centre_cutoff_rejected {i : Fin 60} (A : CellAudit i) {c : Ret 12225}
    (F : BstLean.Part249.FrameInputs 12225 c BstLean.Part249.optionBAgentFrame)
    (hd : F.d ≤ BstLean.Part249.storedFrameCutoff) (hxi : A.centreCap ≤ F.xiF) : False :=
  no_frameInputs_at_stored_cutoff F hd (A.centre_too_large.trans hxi)

end BstLean.Part251
