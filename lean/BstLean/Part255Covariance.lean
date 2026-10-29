import BstLean.Part255Supply
import BstLean.Part255Transfer
import BstLean.Part255Fixed
import BstLean.Part254Interface

/-! The covariance conclusion uses the same selected cell as the event.
The fixed Option B contract has a separate fallback table. -/
namespace BstLean.Part255
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part150 (thetaC)
open BstLean.Part153 (Xi4)
open BstLean.Part254 (cellLower cellUpper worldLower worldUpper Needed)

noncomputable def localCapTable (i : Fin 60) : ℝ := by
  classical
  exact if h : Needed i then localCap ⟨i.val-10,by unfold Needed at h; omega⟩ else 0

noncomputable def cell (i : Fin 60) : Set ℝ :=
  BstLean.Part254.cell i

theorem localCapTable_source (j : Fin 43) : localCapTable (sourceIndex j) = localCap j := by
  have hn : Needed (sourceIndex j) := by
    have := j.isLt
    constructor <;> dsimp [sourceIndex] <;> omega
  simp only [localCapTable,dif_pos hn]
  congr 1

theorem cells_cover {θ : ℝ} (hθ : θ ∈ Icc worldLower worldUpper) :
    ∃ i : Fin 60, Needed i ∧ θ ∈ cell i :=
  ⟨sourceIndex (select θ),select_needed θ,select_member hθ⟩

theorem selected_cap_le {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell i) :
    localCapTable (sourceIndex (select θ)) ≤ localCapTable i := by
  have hn := BstLean.Part254.cell_needed hθ
  rw [localCapTable_source]
  simp only [localCapTable, dif_pos hn]
  apply localCap_mono
  exact select_le_of_mem hθ

theorem localScalar (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ BstLean.Part254.cell (sourceIndex j)) :
    localGaussian (parameters j) θ ≤ localCap j := by
  have hp := parameters_valid j
  have hw := BstLean.Part254.cell_window hθ
  have hθ0 : 0 ≤ θ := by linarith [hw.1]
  have hu : cellUpper (sourceIndex j) ≤ (528/1000 : ℝ) :=
    (min_le_right _ _).trans (by norm_num [worldUpper])
  exact (localGaussian_le_envelope _ hp hw (radii j hθ).1 (radii j hθ).2
    hp.wRadius_lt hp.cRadius_lt).trans
    ((envelope_mono _ hp hθ0 hθ.2 hu hp.wRadius_lt hp.cRadius_lt).trans (grid j).1)

theorem selected_agent_mem {n N : ℕ} (D : Design n) (σ : ℝ → Fin N)
    (E : Fin N → Set (AgFam n)) (k : Ret n)
    (hC : k ∈ agentEv D (BstLean.Part254.selectedEvent σ E)) :
    k ∈ agentEv D (E (σ (thetaC k.1.2 (D.tau0 k)))) := by
  intro ht
  exact hC ht

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
    (hcell : thetaC k.1.2 (D.tau0 k) ∈ BstLean.Part254.cell (sourceIndex j))
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤
      (13/10) * (2/(12225 : ℝ))/12225)
    (hC : k ∈ agentEv D (localEvent (parameters j)
      (cellLower (sourceIndex j)) (cellUpper (sourceIndex j)) payment))
    (v : Fin (mA 12225) → ℝ) :
    Dq k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) v ≤
      localCap j * (2/(12225 : ℝ))/12225 * normSq v := by
  have h := Dq_local_gaussian (parameters j) (parameters_valid j) D k hτ
    (BstLean.Part254.cell_window hcell) hcell hX hC v
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
    exact BstLean.Part254.cell_world hi
  have h := selected_quadratic (BstLean.Part169.paperDesignP 12225) k hτ hw hX hC v
  rw [he] at h
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_right _ (normSq_nonneg v)
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 12225)
  exact mul_le_mul_of_nonneg_right (selected_cap_le hi) (by norm_num)

theorem localCov_contract : BstLean.Part253.LocalCovariance BstLean.Part254.cell capTable :=
  fixedLocalCov

theorem fallback_contract : BstLean.Part253.LocalCovariance cell capTable := by
  intro i θ hn hi c he hτ hC hX v
  exact fixedLocalCov i θ hn hi c he hτ hC hX v

noncomputable def selectedGood (D : Design 12225) : Set (Ret 12225) :=
  agentEv D (selected parameters payment) ∩ agentEv D (BstLean.Part245.MomentM12 12225)

theorem selected_good_charge (D : Design 12225) (hτW : TauWorld D) :
    (retDist D.toCentres).real (selectedGood D)ᶜ ≤ (3/10000 : ℝ) := by
  unfold selectedGood
  rw [compl_inter]
  exact (measureReal_union_le _ _).trans
    ((add_le_add (selected_payment D hτW)
      (BstLean.Part245.moment_M12_ret (by norm_num) D hτW)).trans (by norm_num))

theorem paper_selected_payment :
    (retDist (BstLean.Part169.paperDesignP 12225).toCentres).real
      (agentEv (BstLean.Part169.paperDesignP 12225) (selected parameters payment))ᶜ ≤
        (1/4000 : ℝ) :=
  selected_payment _ (paperDesign_tauWorld _ _ _ _)

theorem paper_selected_good_charge :
    (retDist (BstLean.Part169.paperDesignP 12225).toCentres).real
      (selectedGood (BstLean.Part169.paperDesignP 12225))ᶜ ≤ (3/10000 : ℝ) :=
  selected_good_charge _ (paperDesign_tauWorld _ _ _ _)

theorem selected_covariance_of_good (D : Design 12225) (k : Ret 12225)
    (hτ : 0 < D.tau0 k)
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Icc worldLower worldUpper)
    (hc : k ∈ selectedGood D) :
    COV_at D k (localCapTable (sourceIndex (select (thetaC k.1.2 (D.tau0 k))))) :=
  BstLean.Part199.cov_of_scalar (by norm_num) D k hτ le_rfl
    (selected_quadratic D k hτ hw (hc.2 hτ) hc.1)

end BstLean.Part255
