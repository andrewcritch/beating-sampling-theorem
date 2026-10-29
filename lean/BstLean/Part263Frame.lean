import BstLean.Part263Mass
import BstLean.Part263Events
import BstLean.Part222Supply

namespace BstLean.Part263
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part188
open BstLean.Part160 (AgFam CENTRE_at)
open BstLean.Part169 (paperDesignP)

theorem paper_centre_eq {n : ℕ} (c : Ret n) :
    (paperDesignP n).bA c.1 c.2.1.1 = BstLean.Part211.hiddenCentre (J := n)
      c.2.1.1.1 c.2.1.1.2 c.1.2 ((paperDesignP n).tau0 c) := by
  ext j
  change BstLean.Part150.bT n n c.2.1.1.1 c.2.1.1.2 c.1.2
      ((paperDesignP n).tau0 c) j /
      BstLean.Part150.rhoC c.1.2 ((paperDesignP n).tau0 c) = _
  simp only [BstLean.Part211.hiddenCentre, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem paper_centre_nonneg {n : ℕ} (c : Ret n) (j : Fin (mA n)) :
    0 ≤ (paperDesignP n).bA c.1 c.2.1.1 j := by
  rw [paper_centre_eq]
  exact BstLean.Part222.hiddenCentre_nonneg _ _ _ _ j

/-- These actual network conclusions remain separate from CellCertificate. -/
structure NetworkInputs (n : ℕ) (c : Ret n) (r : CellData) (M H xi : ℝ) : Prop where
  scale_pos : 0 < (paperDesignP n).tau0 c
  centre_pos : 0 < normSq ((paperDesignP n).bA c.1 c.2.1.1)
  interfaces : WFInterfaces (paperDesignP n) c M H xi
  centre_energy : centreEnergy (paperDesignP n) c ≤ r.energy
  full_centre : CENTRE_at (paperDesignP n) c r.centre

noncomputable def frameInputs_from_network {n : ℕ} {event : Set (AgFam n)}
    {cells : Fin 60 → Set ℝ} {caps : Fin 60 → ℝ}
    (C : BstLean.Part259.LocalCovarianceOn event cells caps)
    {c : Ret n} {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ cells i)
    {r : CellData} {M H xi cf : ℝ}
    (S : CellCertificate n M H xi r) (F : NetworkInputs n c r M H xi)
    (hcap : caps i = r.covariance) (hframe : r.frame ≤ cf) :
    BstLean.Part259.LocalFrameInputs n event cells caps c cf where
  cov_le := C
  index := i
  index_needed := hi
  member := hm
  cutoff := fun _ => r.cutoff
  centreAllowance := fun _ => r.centre
  massAllowance := fun _ => 11 / 1000
  M := M
  H := H
  xiP := xi
  E := r.energy
  u := 286 / 100000
  order := 12
  order_pos := by norm_num
  order_le := le_rfl
  scale_pos := F.scale_pos
  centre_pos := F.centre_pos
  centre_nonneg := paper_centre_nonneg c
  interfaces := F.interfaces
  centre_energy := F.centre_energy
  u_pos := by norm_num
  u_lt := by norm_num
  cutoff_pos := S.cutoff_pos
  cutoff_lt := S.cutoff_lt
  gap_pos := S.gap_pos
  covariance_nonneg := by rw [hcap]; exact S.covariance_nonneg
  full_centre := F.full_centre
  mass_scalar := S.mass_scalar
  frame_scalar := by rw [hcap]; exact S.frame_scalar.trans hframe

end BstLean.Part263
