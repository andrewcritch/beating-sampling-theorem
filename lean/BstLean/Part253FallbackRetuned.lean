import BstLean.Part253Fallback
import BstLean.Part253RetunedScalar

/-! The source retuning does not repair the larger supplied covariance caps. -/
namespace BstLean.Part253

noncomputable def certifiedRetunedFrameExpression (i : Fin 60) : ℝ :=
  (BstLean.Part254.capTable i + retunedCentre (centreGroup i)) / retunedCutoff i +
    massTable i

theorem certified_retuned_frame_lower {i : Fin 60} (hi : needed i) :
    (1.489 : ℝ) ≤ certifiedRetunedFrameExpression i := by
  have S := scalar_on_needed hi
  have R := retuned_on_needed hi
  have h := certified_frame_lower hi
  have hnum : 0 ≤ BstLean.Part254.capTable i + centreTable (centreGroup i) := by
    have hh : (1.478 : ℝ) ≤
        (BstLean.Part254.capTable i + centreTable (centreGroup i)) / cutoffTable i := by
      unfold certifiedFrameExpression massTable at h
      linarith
    have hh' := (le_div_iff₀ S.cutoff_pos).mp hh
    nlinarith [S.cutoff_pos]
  apply h.trans
  unfold certifiedFrameExpression certifiedRetunedFrameExpression retunedCentre retunedCutoff
  have hd : 0 < cutoffTable i - 0.0007 := R.cutoff_pos
  gcongr <;> linarith

theorem no_retuned_data_frame {c : BstLean.Part157.Ret 12225}
    (F : LocalFrameInputs BstLean.Part254.cell BstLean.Part254.capTable c
      BstLean.Part249.optionBAgentFrame)
    (hd : F.cutoff = retunedCutoff) (hc : F.centreAllowance = retunedCentre)
    (hm : F.massAllowance = massTable) : False := by
  have h := F.frame_scalar
  rw [hd, hc, hm] at h
  have hl := certified_retuned_frame_lower F.index_needed
  change certifiedRetunedFrameExpression F.index ≤ _ at h
  norm_num [BstLean.Part249.optionBAgentFrame] at h
  linarith

end BstLean.Part253
