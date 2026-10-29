import BstLean.Part271Grid
import BstLean.Part263ScalarSupply
import BstLean.Part264Repair

/-! Scalar cell and frame certificates shared by a closed dimension block. -/
namespace BstLean.Part271.R4

open Real Set BstLean.Part263

structure GridCertificate (lo : ℕ) where
  top : ℝ
  root : ℝ
  upper : ℝ
  lo_pos : 0 < lo
  root_nonneg : 0 ≤ root
  root_square : 12 ≤ root ^ 2 * lo
  denominator_pos : 0 < (1 - 2 * root) + (202831 / 100000 - 1)
  noise_bound : (202831 / 100000 - 1) /
    ((1 - 2 * root) + (202831 / 100000 - 1)) ≤ upper
  top_pos : 46 / 100 < top
  lower_guard : noiseNode top 10 < (472080 / 10^6 : ℝ)
  upper_guard : upper < noiseNode top 53

noncomputable def GridCertificate.grid {lo n : ℕ} (G : GridCertificate lo)
    (hn : lo ≤ n) : Grid :=
  BstLean.Part271.worldGrid
    (BstLean.Part269.noise_upper_bound (N := lo) (R := G.root)
      (by exact_mod_cast hn) (by exact_mod_cast G.lo_pos) G.root_nonneg
      G.root_square G.denominator_pos G.noise_bound)
    G.top G.top_pos G.lower_guard G.upper_guard

theorem GridCertificate.node_le_top {lo : ℕ} (G : GridCertificate lo)
    {j : ℕ} (hj : j ≤ 60) : noiseNode G.top j ≤ G.top := by
  have hjR : (j : ℝ) ≤ 60 := by exact_mod_cast hj
  have h := mul_le_mul_of_nonneg_left hjR (sub_nonneg.mpr G.top_pos.le)
  unfold noiseNode
  linarith

structure CellCertificate (lo hi : ℕ) (M H xi : ℝ) (r : CellData) : Prop where
  lo_pos : 0 < lo
  M_nonneg : 0 ≤ M
  H_nonneg : 0 ≤ H
  xi_nonneg : 0 ≤ xi
  window : r.lower ≤ r.upper
  covariance_nonneg : 0 ≤ r.covariance
  centre_nonneg : 0 ≤ r.centre
  energy_nonneg : 0 ≤ r.energy
  cutoff_pos : 0 < r.cutoff
  cutoff_lt : r.cutoff < (1 - (286 / 100000 : ℝ)) ^ 2
  witness : ∃ a b q : ℝ, 0 ≤ a ∧ r.energy ≤ a ^ 2 ∧
    0 ≤ b ∧ xi / lo ≤ b ^ 2 ∧ 0 < q ∧
    (q + a + b) ^ 2 ≤ (1 - (286 / 100000 : ℝ)) ^ 2 - r.cutoff ∧
    (hi : ℝ) * ((H / (286 / 100000)) ^ 32 +
      BstLean.Part253.rotationPowerCap * (M / lo) ^ 12 / q ^ 24) ≤ 11 / 1000
  frame_scalar : (r.covariance + r.centre) / r.cutoff + 11 / 1000 ≤ r.frame

theorem CellCertificate.at_dimension {lo hi n : ℕ} {M H xi : ℝ} {r : CellData}
    (C : CellCertificate lo hi M H xi r) (hn : n ∈ Icc lo hi) :
    BstLean.Part263.CellCertificate n M H xi r := by
  have hlo : (lo : ℝ) ≤ n := by exact_mod_cast hn.1
  have hhi : (n : ℝ) ≤ hi := by exact_mod_cast hn.2
  have hlop : (0 : ℝ) < lo := by exact_mod_cast C.lo_pos
  have hnp : (0 : ℝ) < n := hlop.trans_le hlo
  have hM0 := C.M_nonneg
  have hH0 := C.H_nonneg
  obtain ⟨a,b,q,ha,hE,hb,hxi,hq,hs,hm⟩ := C.witness
  have hxin : xi / n ≤ b ^ 2 :=
    (div_le_div_of_nonneg_left C.xi_nonneg hlop hlo).trans hxi
  have hMn : M / n ≤ M / lo := div_le_div_of_nonneg_left C.M_nonneg hlop hlo
  have hmass : (n : ℝ) * ((H / (286 / 100000)) ^ 32 +
      BstLean.Part253.rotationPowerCap * (M / n) ^ 12 / q ^ 24) ≤ 11 / 1000 := by
    apply le_trans _ hm
    have hrot : 0 ≤ BstLean.Part253.rotationPowerCap := by
      unfold BstLean.Part253.rotationPowerCap
      positivity
    gcongr
  exact ⟨C.window,C.covariance_nonneg,C.centre_nonneg,C.energy_nonneg,
    C.cutoff_pos,C.cutoff_lt,
    hq.trans_le (BstLean.Part263.gap_lower ha hE hb hxin hq.le hs),
    BstLean.Part263.mass_bound_rational C.M_nonneg ha hE hb hxin hq hs hmass,
    C.frame_scalar⟩

theorem energyBound_antitone {lo n : ℕ} (hl : 0 < lo) (hn : lo ≤ n) :
    energyBound n ≤ energyBound lo := by
  have hlR : (0 : ℝ) < lo := by exact_mod_cast hl
  have hnR : (lo : ℝ) ≤ n := by exact_mod_cast hn
  have hL : layerBound n ≤ layerBound lo := by
    unfold layerBound
    gcongr
  have hL0 : 0 ≤ layerBound n := by unfold layerBound; positivity
  unfold energyBound
  gcongr

theorem energyBound_scaled {lo n : ℕ} (hl : 0 < lo) (hn : lo ≤ n) :
    (n : ℝ) * energyBound n ≤ (lo : ℝ) * energyBound lo := by
  have hlR : (0 : ℝ) < lo := by exact_mod_cast hl
  have hnR : (lo : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := hlR.trans_le hnR
  let A : ℝ := (54477338763354130 / 10^16) * (14142135623730951 / 10^16)
  have identity (k : ℕ) (hk : (0 : ℝ) < k) :
      (k : ℝ) * energyBound k = (13627217491968550 / 10^16 : ℝ) *
        (2 * (A + 5 / (2 * k)) + (A + 5 / (2 * k)) ^ 2 / k) := by
    unfold energyBound layerBound
    dsimp [A]
    field_simp [ne_of_gt hk]
    <;> ring
  rw [identity n hn0, identity lo hlR]
  have hA : 0 ≤ A := by norm_num [A]
  gcongr

theorem cell_energy_mono {n : ℕ} {M H H' xi : ℝ} {r : CellData}
    (C : BstLean.Part263.CellCertificate n M H xi r)
    (hH : 0 ≤ H') (hHH : H' ≤ H) : BstLean.Part263.CellCertificate n M H' xi r := by
  refine ⟨C.window,C.covariance_nonneg,C.centre_nonneg,C.energy_nonneg,
    C.cutoff_pos,C.cutoff_lt,C.gap_pos,?_,C.frame_scalar⟩
  apply le_trans _ C.mass_scalar
  unfold BstLean.Part222.massBoundOrder
  gcongr

structure TableCertificate (lo hi : ℕ) where
  M : ℝ
  H : ℝ
  xi : ℝ
  targetFrame : ℝ
  gridCertificate : GridCertificate lo
  table : Fin 60 → CellData
  certificates : ∀ i, CellCertificate lo hi M H xi (table i)
  energy : energyBound lo ≤ H
  frame : ∀ i, 10 ≤ i.val ∧ i.val ≤ 52 → (table i).frame ≤ targetFrame
  containment : ∀ i, (table i).lower ≤ noiseNode gridCertificate.top i.val ∧
    noiseNode gridCertificate.top (i.val + 1) ≤ (table i).upper

noncomputable def TableCertificate.scalarRow {lo hi n : ℕ} (T : TableCertificate lo hi)
    (hn : n ∈ Icc lo hi) : ScalarRow n where
  M := T.M
  H := T.H * lo / n
  xi := T.xi
  top := T.gridCertificate.top
  targetFrame := T.targetFrame
  table := T.table
  grid := T.gridCertificate.grid hn.1
  grid_top := rfl
  grid_lower := rfl
  grid_upper := rfl
  certificate := by
    intro i
    have hlo : (0 : ℝ) < lo := by exact_mod_cast T.gridCertificate.lo_pos
    have hnR : (lo : ℝ) ≤ n := by exact_mod_cast hn.1
    have hH := (T.certificates i).H_nonneg
    refine cell_energy_mono ((T.certificates i).at_dimension hn) (by positivity) ?_
    apply (div_le_iff₀ (hlo.trans_le hnR)).mpr
    exact mul_le_mul_of_nonneg_left hnR hH
  energy_allowance := by
    have hlo : (0 : ℝ) < lo := by exact_mod_cast T.gridCertificate.lo_pos
    have hnR : (lo : ℝ) ≤ n := by exact_mod_cast hn.1
    have hscaled := (energyBound_scaled T.gridCertificate.lo_pos hn.1).trans
      (mul_le_mul_of_nonneg_left T.energy hlo.le)
    have hn1 : 1 ≤ n := (Nat.succ_le_of_lt T.gridCertificate.lo_pos).trans hn.1
    apply (energy_allowance_bound hn1).trans
    apply (le_div_iff₀ (hlo.trans_le hnR)).mpr
    nlinarith only [hscaled]
  frame := T.frame
  containment := T.containment

theorem envelope_antitone {lo n : ℕ} (hl : 11883 ≤ lo) (hn : lo ≤ n)
    (p : BstLean.Part255.Parameters) (hp : BstLean.Part255.Valid p)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (528 / 1000)) :
    envelope n p θ ≤ envelope lo p θ := by
  have hlR : (11883 : ℝ) ≤ lo := by exact_mod_cast hl
  have hnR : (lo : ℝ) ≤ n := by exact_mod_cast hn
  have hlo : (0 : ℝ) < lo := by linarith
  have hdiv : 4 * θ / n ≤ 4 * θ / lo :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hθ.1) hlo hnR
  have hden : 0 < 1 - 4 * θ / lo := by
    have h := (div_lt_one hlo).mpr (show 4 * θ < (lo : ℝ) by linarith [hθ.2])
    linarith
  have hquot : p.cLam / (1 - 4 * θ / n) ≤ p.cLam / (1 - 4 * θ / lo) :=
    div_le_div_of_nonneg_left hp.cLam_nonneg hden (by linarith)
  unfold envelope
  exact add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hquot (le_refl _)) (le_refl _)) hθ.1) (le_refl _)

structure FrameCertificate {lo hi : ℕ} (T : TableCertificate lo hi) where
  dimension : 11883 ≤ lo
  cap : Fin 43 → ℝ
  cap_nonneg : ∀ j, 0 ≤ cap j
  cap_mono : Monotone cap
  endpoint : ∀ j, envelope lo (BstLean.Part255.parameters j)
    (T.table (BstLean.Part255.sourceIndex j)).upper ≤ cap j
  endpoint_range : ∀ j, (T.table (BstLean.Part255.sourceIndex j)).upper ∈
    Icc (0 : ℝ) (528 / 1000)
  frame : ∀ j, (cap j + (T.table (BstLean.Part255.sourceIndex j)).centre) /
    (T.table (BstLean.Part255.sourceIndex j)).cutoff + 11 / 1000 ≤ T.targetFrame

noncomputable def FrameCertificate.repair {lo hi n : ℕ} {T : TableCertificate lo hi}
    (F : FrameCertificate T) (hn : n ∈ Icc lo hi) :
    BstLean.Part264.FrameRepair n (T.scalarRow hn) where
  cap := F.cap
  cap_nonneg := F.cap_nonneg
  cap_mono := F.cap_mono
  endpoint := fun j => (envelope_antitone F.dimension hn.1 _
    (BstLean.Part255.parameters_valid j) (F.endpoint_range j)).trans (F.endpoint j)
  endpoint_upper := fun j => (F.endpoint_range j).2
  frame := F.frame

end BstLean.Part271.R4
