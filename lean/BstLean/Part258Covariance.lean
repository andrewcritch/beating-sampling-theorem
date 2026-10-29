import BstLean.Part258Table

/-! Covariance uses the event on the exact World cells. -/
namespace BstLean.Part258
open MeasureTheory Real Set BstLean.Part255
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part150 (thetaC)
open BstLean.Part153 (Xi4)

noncomputable def localCapTable (i : Fin 60) : ℝ := by
  classical
  exact if h : Needed i then cap ⟨i.val-10,by unfold Needed at h; omega⟩ else 0

theorem localCapTable_source (j : Fin 43) : localCapTable (sourceIndex j) = cap j := by
  have hn : Needed (sourceIndex j) := by
    have := j.isLt
    constructor <;> dsimp [sourceIndex] <;> omega
  simp only [localCapTable,dif_pos hn]
  congr 1

theorem selected_cap_le {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell i) :
    localCapTable (sourceIndex (select θ)) ≤ localCapTable i := by
  have hn := cell_needed hθ
  rw [localCapTable_source]
  simp only [localCapTable, dif_pos hn]
  apply cap_mono
  exact select_le_of_mem hθ

theorem selected_agent_local (p : Fin 43 → Parameters) (ε : ℝ)
    (D : Design 12225) (k : Ret 12225)
    (hC : k ∈ agentEv D (selected p ε)) :
    k ∈ agentEv D (localEvent (p (select (thetaC k.1.2 (D.tau0 k))))
      (cellLower (sourceIndex (select (thetaC k.1.2 (D.tau0 k)))))
      (cellUpper (sourceIndex (select (thetaC k.1.2 (D.tau0 k))))) ε) :=
  selected_agent_mem D select (fun j => localEvent (p j)
    (cellLower (sourceIndex j)) (cellUpper (sourceIndex j)) ε) k hC

theorem indexed_quadratic (j : Fin 43) (D : Design 12225) (k : Ret 12225)
    (hτ : 0 < D.tau0 k)
    (hcell : thetaC k.1.2 (D.tau0 k) ∈ cell (sourceIndex j))
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤
      (13/10) * (2/(12225 : ℝ))/12225)
    (hC : k ∈ agentEv D (localEvent (parameters j)
      (cellLower (sourceIndex j)) (cellUpper (sourceIndex j)) payment))
    (v : Fin (mA 12225) → ℝ) :
    Dq k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) v ≤
      cap j * (2/(12225 : ℝ))/12225 * normSq v := by
  have h := Dq_local_gaussian (parameters j) (parameters_valid j) D k hτ
    (cell_window hcell) hcell hX hC v
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_right _ (normSq_nonneg v)
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 12225)
  exact mul_le_mul_of_nonneg_right (localScalar j hcell) (by norm_num)

theorem selected_quadratic (D : Design 12225) (k : Ret 12225)
    (hτ : 0 < D.tau0 k)
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Icc worldLower worldUpper)
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤
      (13/10) * (2/(12225 : ℝ))/12225)
    (hC : k ∈ agentEv D (selected parameters payment)) (v : Fin (mA 12225) → ℝ) :
    Dq k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) v ≤
      localCapTable (sourceIndex (select (thetaC k.1.2 (D.tau0 k)))) *
        (2/(12225 : ℝ))/12225 * normSq v := by
  rw [localCapTable_source]
  exact indexed_quadratic _ D k hτ (select_member hw) hX
    (selected_agent_local parameters payment D k hC) v

theorem localCov : LocalCovarianceOn (selected parameters payment) cell localCapTable := by
  intro i θ _ hi k he hτ hC hX v
  have hw : thetaC k.1.2 ((BstLean.Part169.paperDesignP 12225).tau0 k) ∈
      Icc worldLower worldUpper := by
    rw [he]
    exact cell_world hi
  have h := selected_quadratic (BstLean.Part169.paperDesignP 12225) k hτ hw hX hC v
  rw [he] at h
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_right _ (normSq_nonneg v)
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 12225)
  exact mul_le_mul_of_nonneg_right (selected_cap_le hi) (by norm_num)


end BstLean.Part258
