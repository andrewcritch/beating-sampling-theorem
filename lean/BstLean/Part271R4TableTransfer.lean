import BstLean.Part271R4Block

/-! Reuse one conservative scalar table on blocks of at most ten dimensions. -/
namespace BstLean.Part271.R4
open Real Set BstLean.Part263

theorem block_mass_scaled {base lo hi : ℕ} (hb : 0 < base) (hl : base ≤ lo)
    (hw : hi ≤ lo + 9) {M H q : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H) (hq : 0 < q) :
    (hi : ℝ) * (((H * base / lo) / (286 / 100000)) ^ 32 +
      BstLean.Part253.rotationPowerCap * (M / lo) ^ 12 / q ^ 24) ≤
    ((base : ℝ) + 9) * ((H / (286 / 100000)) ^ 32 +
      BstLean.Part253.rotationPowerCap * (M / base) ^ 12 / q ^ 24) := by
  have hbR : (0 : ℝ) < base := by exact_mod_cast hb
  have hlR : (base : ℝ) ≤ lo := by exact_mod_cast hl
  have hlo : (0 : ℝ) < lo := hbR.trans_le hlR
  have hhi : (hi : ℝ) ≤ (lo : ℝ) + 9 := by exact_mod_cast hw
  let s : ℝ := (base : ℝ) / lo
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := (div_le_one hlo).mpr hlR
  have hs32 : s ^ 32 ≤ s := pow_le_of_le_one hs0 hs1 (by decide)
  have hs12 : s ^ 12 ≤ s := pow_le_of_le_one hs0 hs1 (by decide)
  have his : (hi : ℝ) * s ≤ (base : ℝ) + 9 := by
    calc
      (hi : ℝ) * s ≤ ((lo : ℝ) + 9) * s := mul_le_mul_of_nonneg_right hhi hs0
      _ = (base : ℝ) + 9 * s := by dsimp [s]; field_simp [ne_of_gt hlo] <;> ring
      _ ≤ (base : ℝ) + 9 := by linarith only [hs1]
  have eH : ((H * base / lo) / (286 / 100000)) ^ 32 =
      (H / (286 / 100000)) ^ 32 * s ^ 32 := by
    rw [← mul_pow]
    congr 1
    dsimp [s]
    ring
  have eM : M / (lo : ℝ) = (M / base) * s := by
    dsimp [s]
    field_simp [ne_of_gt hbR,ne_of_gt hlo]
    <;> ring
  let A : ℝ := (H / (286 / 100000)) ^ 32
  let B : ℝ := BstLean.Part253.rotationPowerCap * (M / base) ^ 12 / q ^ 24
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; unfold BstLean.Part253.rotationPowerCap; positivity
  calc
    _ = (hi : ℝ) * (A * s ^ 32 + B * s ^ 12) := by
      dsimp [A,B]
      rw [eH,eM,mul_pow]
      ring
    _ ≤ (hi : ℝ) * (A * s + B * s) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hs32 hA)
          (mul_le_mul_of_nonneg_left hs12 hB)) (Nat.cast_nonneg hi)
    _ = ((hi : ℝ) * s) * (A + B) := by ring
    _ ≤ ((base : ℝ) + 9) * (A + B) :=
      mul_le_mul_of_nonneg_right his (add_nonneg hA hB)

theorem CellCertificate.onBlock {base lo hi : ℕ} {M H xi : ℝ} {r : CellData}
    (C : CellCertificate base (base+9) M H xi r) (hl : base ≤ lo) (hw : hi ≤ lo+9) :
    CellCertificate lo hi M (H * base / lo) xi r := by
  have hbR : (0 : ℝ) < base := by exact_mod_cast C.lo_pos
  have hlR : (base : ℝ) ≤ lo := by exact_mod_cast hl
  have hH := C.H_nonneg
  obtain ⟨a,b,q,ha,hE,hb,hxi,hq,hcut,hmass⟩ := C.witness
  refine ⟨by have := C.lo_pos; omega,C.M_nonneg,by positivity,C.xi_nonneg,C.window,C.covariance_nonneg,
    C.centre_nonneg,C.energy_nonneg,C.cutoff_pos,C.cutoff_lt,?_,C.frame_scalar⟩
  refine ⟨a,b,q,ha,hE,hb,?_,hq,hcut,?_⟩
  · exact (div_le_div_of_nonneg_left C.xi_nonneg hbR hlR).trans hxi
  · apply (block_mass_scaled C.lo_pos hl hw C.M_nonneg C.H_nonneg hq).trans
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hmass

noncomputable def TableCertificate.onBlock {base lo hi : ℕ}
    (T : TableCertificate base (base+9)) (hl : base ≤ lo) (hw : hi ≤ lo+9)
    (G : GridCertificate lo)
    (hcontain : ∀ i, (T.table i).lower ≤ noiseNode G.top i.val ∧
      noiseNode G.top (i.val+1) ≤ (T.table i).upper) : TableCertificate lo hi where
  M := T.M
  H := T.H * base / lo
  xi := T.xi
  targetFrame := T.targetFrame
  gridCertificate := G
  table := T.table
  certificates := fun i => (T.certificates i).onBlock hl hw
  energy := by
    have hbR : (0 : ℝ) < base := by exact_mod_cast T.gridCertificate.lo_pos
    have hlR : (base : ℝ) ≤ lo := by exact_mod_cast hl
    have h := (energyBound_scaled T.gridCertificate.lo_pos hl).trans
      (mul_le_mul_of_nonneg_left T.energy hbR.le)
    apply (le_div_iff₀ (hbR.trans_le hlR)).mpr
    nlinarith only [h]
  frame := T.frame
  containment := hcontain

noncomputable def FrameCertificate.onBlock {base lo hi : ℕ}
    {T : TableCertificate base (base+9)} (F : FrameCertificate T)
    (hl : base ≤ lo) (hw : hi ≤ lo+9) (G : GridCertificate lo)
    (hcontain : ∀ i, (T.table i).lower ≤ noiseNode G.top i.val ∧
      noiseNode G.top (i.val+1) ≤ (T.table i).upper) :
    FrameCertificate (T.onBlock hl hw G hcontain) where
  dimension := F.dimension.trans hl
  cap := F.cap
  cap_nonneg := F.cap_nonneg
  cap_mono := F.cap_mono
  endpoint := fun j => (envelope_antitone F.dimension hl _
    (BstLean.Part255.parameters_valid j) (F.endpoint_range j)).trans (F.endpoint j)
  endpoint_range := F.endpoint_range
  frame := F.frame

end BstLean.Part271.R4
