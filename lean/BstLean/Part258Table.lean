import BstLean.Part258Events
import BstLean.Part255Covariance

/-! The final cap uses an outward rational enclosure of the exact endpoint. -/
namespace BstLean.Part258
open Real Set BstLean.Part255
open BstLean.Part251 (noiseNode noiseNode_mono proposedThetaUpper)

noncomputable def lastCap : ℝ := 291825275/10^9
noncomputable def cap (j : Fin 43) : ℝ :=
  if j.val = 42 then lastCap else localCap j
noncomputable def endpoint (j : Fin 43) : ℝ :=
  if j.val = 42 then 523141/10^6 else BstLean.Part254.cellUpper (sourceIndex j)

theorem last_grid :
    envelope (parameters ⟨42, by decide⟩) (523141/10^6) ≤ lastCap ∧
    lastCap - 1/10^9 < envelope (parameters ⟨42, by decide⟩) (523141/10^6) ∧
    0 ≤ lastCap := by
  norm_num [envelope, parameters, lastCap]

theorem old_last_le : localCap ⟨42, by decide⟩ ≤ lastCap := by
  norm_num [localCap, lastCap]

theorem cap_nonneg (j : Fin 43) : 0 ≤ cap j := by
  unfold cap
  split
  · exact last_grid.2.2
  · exact (BstLean.Part255.grid j).2.2

theorem cap_ge (j : Fin 43) : localCap j ≤ cap j := by
  unfold cap
  split
  · have he : j = ⟨42, by decide⟩ := Fin.ext (by assumption)
    subst j
    exact old_last_le
  · exact le_rfl

theorem cap_mono {a b : Fin 43} (hab : a.val ≤ b.val) : cap a ≤ cap b := by
  by_cases hb : b.val = 42
  · have hbe : b = ⟨42, by decide⟩ := Fin.ext hb
    subst b
    by_cases ha : a.val = 42
    · have hae : a = ⟨42, by decide⟩ := Fin.ext ha
      subst a
      exact le_rfl
    · rw [cap, if_neg ha, cap, if_pos rfl]
      exact (localCap_mono hab).trans old_last_le
  · have ha : a.val ≠ 42 := by have := b.isLt; omega
    simpa only [cap, if_neg hb, if_neg ha] using localCap_mono hab

theorem grid (j : Fin 43) : envelope (parameters j) (endpoint j) ≤ cap j := by
  by_cases hj : j.val = 42
  · have he : j = ⟨42, by decide⟩ := Fin.ext hj
    subst j
    exact last_grid.1
  · simpa only [endpoint, cap, if_neg hj] using (BstLean.Part255.grid j).1

theorem endpoint_le (j : Fin 43) : endpoint j ≤ (528/1000 : ℝ) := by
  unfold endpoint
  split
  · norm_num
  · exact (min_le_right _ _).trans (by norm_num [BstLean.Part254.worldUpper])

theorem cell_endpoint (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell (sourceIndex j)) : θ ≤ endpoint j := by
  by_cases hj : j.val = 42
  · simpa only [endpoint, if_pos hj] using (cell_world hθ).2.trans upper_bound
  · have hn : (sourceIndex j).val + 1 ≤ 52 := by
      have := j.isLt
      dsimp [sourceIndex]
      omega
    have hu := (cell_source hθ).2
    change θ ≤ noiseNode ((sourceIndex j).val + 1) at hu
    have hb : noiseNode ((sourceIndex j).val + 1) ≤ BstLean.Part254.worldUpper :=
      (noiseNode_mono hn).trans (by
        norm_num [noiseNode, proposedThetaUpper, BstLean.Part254.worldUpper])
    simpa only [endpoint, if_neg hj, BstLean.Part254.cellUpper] using le_min hu (hu.trans hb)

theorem localScalar (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell (sourceIndex j)) : localGaussian (parameters j) θ ≤ cap j := by
  have hp := parameters_valid j
  have hw := cell_window hθ
  have hθ0 : 0 ≤ θ := by linarith [hw.1]
  have hr := radii j (cell_source hθ)
  exact (localGaussian_le_envelope _ hp hw hr.1 hr.2
    hp.wRadius_lt hp.cRadius_lt).trans
    ((envelope_mono _ hp hθ0 (cell_endpoint j hθ) (endpoint_le j)
      hp.wRadius_lt hp.cRadius_lt).trans (grid j))

end BstLean.Part258
