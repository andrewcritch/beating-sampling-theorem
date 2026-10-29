import BstLean.Part263Transfer
import BstLean.Part263Cells

/-! The selected-event contract keeps each analytic table obligation explicit. -/
namespace BstLean.Part263
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part150 (thetaC)
open BstLean.Part153 (Xi4)
open BstLean.Part255 (Parameters Valid payment sourceIndex)
open BstLean.Part199 (exampleWide exampleCore radiusMinus)

structure CovarianceInputs (n : ℕ) (G : Grid) (p : Fin 43 → Parameters)
    (caps : Fin 60 → ℝ) : Prop where
  supplies : ∀ j, Supply n (p j) (cellLower G (sourceIndex j)) (cellUpper G (sourceIndex j))
  world_window : Icc G.worldLower G.worldUpper ⊆ Icc (46 / 100 : ℝ) (528 / 1000)
  wide_radius : ∀ j θ, θ ∈ cell G (sourceIndex j) → radiusMinus n θ exampleWide ≤ (p j).wRadius
  core_radius : ∀ j θ, θ ∈ cell G (sourceIndex j) → radiusMinus n θ exampleCore ≤ (p j).cRadius
  scalar : ∀ i θ, θ ∈ cell G i → envelope n (p (select G.top θ)) θ ≤ caps i

noncomputable def covarianceEvent (n : ℕ) (G : Grid) (p : Fin 43 → Parameters) :
    Set (AgFam n) :=
  selected (select G.top) p (fun j => cellLower G (sourceIndex j))
    (fun j => cellUpper G (sourceIndex j)) payment

theorem covarianceEvent_measurable (n : ℕ) (G : Grid) (p : Fin 43 → Parameters) :
    MeasurableSet (covarianceEvent n G p) :=
  selected_measurable _ (select_measurable G.top) _ _ _ _

theorem covarianceEvent_payment {n : ℕ} (hn : 2 ≤ n) {G : Grid}
    {p : Fin 43 → Parameters} {caps : Fin 60 → ℝ} (F : CovarianceInputs n G p caps) :
    (retDist (BstLean.Part169.paperDesignP n).toCentres).real
      (agentEv (BstLean.Part169.paperDesignP n) (covarianceEvent n G p))ᶜ ≤
        (1 / 4000 : ℝ) :=
  selected_payment hn _ (select_measurable G.top) _ _ _ F.supplies

theorem localCov {n : ℕ} (hn : 11883 ≤ n) {G : Grid}
    {p : Fin 43 → Parameters} {caps : Fin 60 → ℝ} (F : CovarianceInputs n G p caps) :
    BstLean.Part259.LocalCovarianceOn (covarianceEvent n G p) (cell G) caps := by
  intro i θ _ hi k he hτ hC hX v
  let j := select G.top θ
  have hw : θ ∈ Icc G.worldLower G.worldUpper := cell_world hi
  have hmem : θ ∈ cell G (sourceIndex j) := select_member G hw
  have hp := (F.supplies j).valid
  have hlocal : k ∈ agentEv (BstLean.Part169.paperDesignP n)
      (localEvent n (p j) (cellLower G (sourceIndex j)) (cellUpper G (sourceIndex j)) payment) := by
    have h := BstLean.Part255.selected_agent_mem (BstLean.Part169.paperDesignP n)
      (select G.top)
      (fun j => localEvent n (p j) (cellLower G (sourceIndex j)) (cellUpper G (sourceIndex j)) payment)
      k hC
    simpa only [he] using h
  have hgauss := Dq_local_gaussian hn (p j) hp (BstLean.Part169.paperDesignP n) k hτ
    (by rw [he]; exact F.world_window hw) (by rw [he]; exact hmem) hX hlocal v
  rw [he] at hgauss
  have hscalar := (localGaussian_le_envelope hn (p j) hp (F.world_window hw)
    (F.wide_radius j θ hmem) (F.core_radius j θ hmem) hp.wRadius_lt hp.cRadius_lt).trans
    (F.scalar i θ hi)
  refine hgauss.trans ?_
  apply mul_le_mul_of_nonneg_right _ (normSq_nonneg v)
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ n)
  exact mul_le_mul_of_nonneg_right hscalar (by positivity : (0 : ℝ) ≤ 2 / n)

end BstLean.Part263
