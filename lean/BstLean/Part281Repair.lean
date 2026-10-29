import BstLean.Part281Parameters
import BstLean.Part263ScalarSupply
import BstLean.Part263Covariance

/-! Increasing covariance caps can retain the original local frame allowance. -/
namespace BstLean.Part281
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part160
open BstLean.Part255 (sourceIndex)
open BstLean.Part281.TI (parameters parameters_valid)
open BstLean.Part263

structure FrameRepair (n : ℕ) (R : ScalarRow n) where
  cap : Fin 43 → ℝ
  cap_nonneg : ∀ j, 0 ≤ cap j
  cap_mono : Monotone cap
  endpoint : ∀ j, envelope n (parameters j) (R.table (sourceIndex j)).upper ≤ cap j
  endpoint_upper : ∀ j, (R.table (sourceIndex j)).upper ≤ 528 / 1000
  frame : ∀ j, (cap j + (R.table (sourceIndex j)).centre) /
    (R.table (sourceIndex j)).cutoff + 11 / 1000 ≤ R.targetFrame

theorem select_le_of_mem {G : Grid} {i : Fin 60} {θ : ℝ} (hθ : θ ∈ cell G i) :
    (select G.top θ).val ≤ i.val - 10 := by
  have hn10 : 10 ≤ i.val := (cell_needed hθ).1
  have hu : θ ≤ noiseNode G.top (i.val + 1) := hθ.2.trans (min_le_left _ _)
  have he : noiseNode G.top (i.val + 1) = noiseNode G.top 10 +
      noiseStep G.top * ((i.val - 10 + 1 : ℕ) : ℝ) := by
    have h := noiseNode_add G.top (i.val - 10 + 1)
    rw [show i.val - 10 + 1 + 10 = i.val + 1 by omega] at h
    exact h
  have hr : (θ - noiseNode G.top 10) / noiseStep G.top ≤
      ((i.val - 10 + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ (noiseStep_pos G)]
    rw [he] at hu
    linarith
  have hceil : Nat.ceil ((θ - noiseNode G.top 10) / noiseStep G.top) ≤
      i.val - 10 + 1 := Nat.ceil_le.mpr hr
  change min 42 (Nat.ceil ((θ - noiseNode G.top 10) / noiseStep G.top) - 1) ≤ i.val - 10
  exact (min_le_right _ _).trans (by omega)

noncomputable def caps {n : ℕ} {R : ScalarRow n} (F : FrameRepair n R) (i : Fin 60) : ℝ :=
  if h : 10 ≤ i.val ∧ i.val ≤ 52 then F.cap ⟨i.val - 10, by omega⟩ else 0

theorem caps_source {n : ℕ} {R : ScalarRow n} (F : FrameRepair n R) (j : Fin 43) :
    caps F (sourceIndex j) = F.cap j := by
  have hi : 10 ≤ (sourceIndex j).val ∧ (sourceIndex j).val ≤ 52 := by
    dsimp [sourceIndex]
    omega
  simp only [caps, dif_pos hi]
  congr 1

theorem envelope_on_cell {n : ℕ} (hn : 11883 ≤ n) {R : ScalarRow n}
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
  exact (envelope_mono hn _ (parameters_valid j) hθ0 hs.2 (F.endpoint_upper j)
    (parameters_valid j).wRadius_lt (parameters_valid j).cRadius_lt).trans (F.endpoint j)

theorem selected_envelope {n : ℕ} (hn : 11883 ≤ n) {R : ScalarRow n}
    (F : FrameRepair n R) (i : Fin 60) {θ : ℝ} (hθ : θ ∈ cell R.grid i) :
    envelope n (parameters (select R.grid.top θ)) θ ≤ caps F i := by
  have hw := cell_world hθ
  have hs := envelope_on_cell hn F (select R.grid.top θ) (select_member R.grid hw)
  have hi := cell_needed hθ
  rw [caps, dif_pos hi]
  exact hs.trans (F.cap_mono (select_le_of_mem hθ))

noncomputable def repairedCell (r : CellData) (cov cf : ℝ) : CellData :=
  { r with covariance := cov, frame := cf }

theorem repair_certificate {n : ℕ} {M H xi cov cf : ℝ} {r : CellData}
    (C : CellCertificate n M H xi r) (hc : 0 ≤ cov)
    (hf : (cov + r.centre) / r.cutoff + 11 / 1000 ≤ cf) :
    CellCertificate n M H xi (repairedCell r cov cf) := by
  exact ⟨C.window,hc,C.centre_nonneg,C.energy_nonneg,C.cutoff_pos,C.cutoff_lt,
    C.gap_pos,C.mass_scalar,hf⟩

end BstLean.Part281
