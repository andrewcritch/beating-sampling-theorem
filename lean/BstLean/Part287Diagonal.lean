import BstLean.Part271R4Block

/-! Reuse a conservative table at every larger dimension.
The singleton certificate at n scales the energy allowance by base/n.
No list of dimensions, square-root evaluation, or short-block partition is needed. -/
namespace BstLean.Part287.Diagonal

open Real Set BstLean.Part263 BstLean.Part271.R4

noncomputable def promoteGrid {base n : ℕ} (G : GridCertificate base)
    (hn : base ≤ n) : GridCertificate n where
  top := G.top
  root := G.root
  upper := G.upper
  lo_pos := lt_of_lt_of_le G.lo_pos hn
  root_nonneg := G.root_nonneg
  root_square := G.root_square.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (sq_nonneg G.root))
  denominator_pos := G.denominator_pos
  noise_bound := G.noise_bound
  top_pos := G.top_pos
  lower_guard := G.lower_guard
  upper_guard := G.upper_guard

/-- The powers 32 and 12 absorb the dimension factor after scaling. -/
theorem scaled_mass {base n : ℕ} (hb : 0 < base) (hn : base ≤ n)
    {M H q : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H) (hq : 0 < q) :
    (n : ℝ) * (((H * base / n) / (286 / 100000)) ^ 32 +
      BstLean.Part253.rotationPowerCap * (M / n) ^ 12 / q ^ 24) ≤
    (base : ℝ) * ((H / (286 / 100000)) ^ 32 +
      BstLean.Part253.rotationPowerCap * (M / base) ^ 12 / q ^ 24) := by
  have hbR : (0 : ℝ) < base := by exact_mod_cast hb
  have hnR : (base : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := hbR.trans_le hnR
  let s : ℝ := (base : ℝ) / n
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := (div_le_one hn0).mpr hnR
  have hs32 : s ^ 32 ≤ s := pow_le_of_le_one hs0 hs1 (by decide)
  have hs12 : s ^ 12 ≤ s := pow_le_of_le_one hs0 hs1 (by decide)
  have hns : (n : ℝ) * s = base := by
    dsimp [s]
    field_simp [ne_of_gt hn0] <;> ring
  have eH : ((H * base / n) / (286 / 100000)) ^ 32 =
      (H / (286 / 100000)) ^ 32 * s ^ 32 := by
    rw [← mul_pow]
    congr 1
    dsimp [s]
    ring
  have eM : M / (n : ℝ) = (M / base) * s := by
    dsimp [s]
    field_simp [ne_of_gt hbR, ne_of_gt hn0] <;> ring
  let A : ℝ := (H / (286 / 100000)) ^ 32
  let B : ℝ := BstLean.Part253.rotationPowerCap * (M / base) ^ 12 / q ^ 24
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    unfold BstLean.Part253.rotationPowerCap
    positivity
  calc
    _ = (n : ℝ) * (A * s ^ 32 + B * s ^ 12) := by
      dsimp [A, B]
      rw [eH, eM, mul_pow]
      ring
    _ ≤ (n : ℝ) * (A * s + B * s) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hs32 hA)
          (mul_le_mul_of_nonneg_left hs12 hB)) (Nat.cast_nonneg n)
    _ = ((n : ℝ) * s) * (A + B) := by ring
    _ = _ := by rw [hns]

theorem diagonalCell {base hi n : ℕ} {M H xi : ℝ} {r : CellData}
    (C : BstLean.Part271.R4.CellCertificate base hi M H xi r)
    (hbase : base ≤ hi) (hn : base ≤ n) :
    BstLean.Part271.R4.CellCertificate n n M (H * base / n) xi r := by
  have hbR : (0 : ℝ) < base := by exact_mod_cast C.lo_pos
  have hnR : (base : ℝ) ≤ n := by exact_mod_cast hn
  have hhiR : (base : ℝ) ≤ hi := by exact_mod_cast hbase
  have hH := C.H_nonneg
  obtain ⟨a, b, q, ha, hE, hb, hxi, hq, hcut, hmass⟩ := C.witness
  refine ⟨lt_of_lt_of_le C.lo_pos hn, C.M_nonneg, by positivity,
    C.xi_nonneg, C.window, C.covariance_nonneg, C.centre_nonneg,
    C.energy_nonneg, C.cutoff_pos, C.cutoff_lt, ?_, C.frame_scalar⟩
  refine ⟨a, b, q, ha, hE, hb, ?_, hq, hcut, ?_⟩
  · exact (div_le_div_of_nonneg_left C.xi_nonneg hbR hnR).trans hxi
  · refine (scaled_mass C.lo_pos hn C.M_nonneg C.H_nonneg hq).trans ?_
    refine le_trans (mul_le_mul_of_nonneg_right hhiR ?_) hmass
    unfold BstLean.Part253.rotationPowerCap
    positivity

noncomputable def diagonalTable {base hi n : ℕ} (T : TableCertificate base hi)
    (hbase : base ≤ hi) (hn : base ≤ n) : TableCertificate n n where
  M := T.M
  H := T.H * base / n
  xi := T.xi
  targetFrame := T.targetFrame
  gridCertificate := promoteGrid T.gridCertificate hn
  table := T.table
  certificates := fun i => diagonalCell (T.certificates i) hbase hn
  energy := by
    have hbR : (0 : ℝ) < base := by exact_mod_cast T.gridCertificate.lo_pos
    have hnR : (base : ℝ) ≤ n := by exact_mod_cast hn
    have h := (energyBound_scaled T.gridCertificate.lo_pos hn).trans
      (mul_le_mul_of_nonneg_left T.energy hbR.le)
    apply (le_div_iff₀ (hbR.trans_le hnR)).mpr
    nlinarith only [h]
  frame := T.frame
  containment := T.containment

noncomputable def diagonalFrame {base hi n : ℕ} {T : TableCertificate base hi}
    (F : FrameCertificate T) (hbase : base ≤ hi) (hn : base ≤ n) :
    FrameCertificate (diagonalTable T hbase hn) where
  dimension := F.dimension.trans hn
  cap := F.cap
  cap_nonneg := F.cap_nonneg
  cap_mono := F.cap_mono
  endpoint := fun j => (envelope_antitone F.dimension hn _
    (BstLean.Part255.parameters_valid j) (F.endpoint_range j)).trans (F.endpoint j)
  endpoint_range := F.endpoint_range
  frame := F.frame

noncomputable def scalarRow {base hi n : ℕ} (T : TableCertificate base hi)
    (hbase : base ≤ hi) (hn : base ≤ n) : ScalarRow n :=
  (diagonalTable T hbase hn).scalarRow ⟨le_rfl, le_rfl⟩

theorem scalarRow_energy {base hi n : ℕ} (T : TableCertificate base hi)
    (hbase : base ≤ hi) (hn : base ≤ n) :
    (scalarRow T hbase hn).H = T.H * base / n := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le T.gridCertificate.lo_pos hn))
  change (T.H * base / n) * n / n = T.H * base / n
  rw [div_mul_cancel₀ _ hn0]

theorem scalarRow_top {base hi n : ℕ} (T : TableCertificate base hi)
    (hbase : base ≤ hi) (hn : base ≤ n) :
    (scalarRow T hbase hn).grid.top = T.gridCertificate.top := rfl

end BstLean.Part287.Diagonal
