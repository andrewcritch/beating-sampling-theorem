import BstLean.Part262Root

/-! A variable-dimension low-mass reduction uses the actual direction,
energy and parallel interfaces. The local source supplies remain separate. -/
namespace BstLean.Part262
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part188 BstLean.Part195 BstLean.Part222
open BstLean.Part252 (mixtureFloor lowMassBudget)

theorem paper_centre_eq {n : ℕ} (c : Ret n) :
    (paperDesignP n).bA c.1 c.2.1.1 = BstLean.Part211.hiddenCentre (J := n)
      c.2.1.1.1 c.2.1.1.2 c.1.2 ((paperDesignP n).tau0 c) := by
  ext j
  change BstLean.Part150.bT n n c.2.1.1.1 c.2.1.1.2 c.1.2
      ((paperDesignP n).tau0 c) j /
      BstLean.Part150.rhoC c.1.2 ((paperDesignP n).tau0 c) = _
  simp only [BstLean.Part211.hiddenCentre, Pi.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

theorem paper_centre_nonneg {n : ℕ} (c : Ret n) (j : Fin (mA n)) :
    0 ≤ (paperDesignP n).bA c.1 c.2.1.1 j := by
  rw [paper_centre_eq]
  exact hiddenCentre_nonneg _ _ _ _ j

def LowResidualMass {n : ℕ} (c : Ret n) : Prop :=
  ∫ a, (stdGauss (Fin (n - 1))).real
    {v | BstLean.Part162.sgA (paperDesignP n) c a v < √(2 / (n : ℝ) * mixtureFloor)}
      ∂muI n ≤ lowMassBudget

theorem low_mass_gap {n : ℕ} (hn : 12225 ≤ n) :
    (4 / 100 : ℝ) ≤ √((1 - 42 / 10000) ^ 2 - mixtureFloor) -
      (√(702 / 1000) + √((4 / 100 : ℝ) / n)) := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (880019 / 10 ^ 6 : ℝ) ≤ √((1 - 42 / 10000) ^ 2 - mixtureFloor) :=
    le_sqrt_of_sq_le (by norm_num [mixtureFloor])
  have h2 : √(702 / 1000 : ℝ) ≤ 837855 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  have h3 : √((4 / 100 : ℝ) / n) ≤ 181 / 10 ^ 5 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR).trans (by norm_num)
  linarith

theorem low_mass_price {n : ℕ} (hn : 12225 ≤ n) :
    massBound n (91 / 1000) ((2101 / 100) / n) (4 / 100) (702 / 1000)
      (42 / 10000) mixtureFloor ≤ n * lowMassBudget := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hg := low_mass_gap hn
  have hg0 : 0 < √((1 - 42 / 10000) ^ 2 - mixtureFloor) -
      (√(702 / 1000) + √((4 / 100 : ℝ) / n)) := by linarith
  have hr := BstLean.Part252.rotation_twelve
  have hr0 := rotationConstant_nonneg 12
  unfold massBound
  apply mul_le_mul_of_nonneg_left _ hn0
  calc
    _ ≤ (((2101 / 100 : ℝ) / n) / (42 / 10000)) ^ 32 +
        ((48 / 10 : ℝ) ^ 24 * ((91 / 1000) / n) ^ 12) / (4 / 100) ^ 24 := by
      have hd := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4 / 100) hg 24
      have hm := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr0 hr 24)
        (by positivity : (0 : ℝ) ≤ ((91 / 1000) / n) ^ 12)
      exact add_le_add_right (div_le_div₀ (by positivity) hm (by positivity) hd)
        ((((2101 / 100 : ℝ) / n) / (42 / 10000)) ^ 32)
    _ ≤ (((2101 / 100 : ℝ) / 12225) / (42 / 10000)) ^ 32 +
        ((48 / 10 : ℝ) ^ 24 * ((91 / 1000) / 12225) ^ 12) / (4 / 100) ^ 24 := by
      gcongr <;> norm_num
    _ ≤ lowMassBudget := by norm_num [lowMassBudget]

theorem low_mass_of_interfaces {n : ℕ} (hn : 12225 ≤ n) {c : Ret n}
    (hw : WINDOW (paperDesignP n) c) (he : 0 < eR c)
    (I : WFInterfaces (paperDesignP n) c (91 / 1000) ((2101 / 100) / n) (4 / 100))
    (hE : centreEnergy (paperDesignP n) c ≤ 702 / 1000) : LowResidualMass c := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb : 0 < normSq ((paperDesignP n).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by linarith)
  have hg := low_mass_gap hn
  have hm := sharp_residual_mass (d := mixtureFloor) (by omega) (paperDesignP n) c hw.2.1 hb
    (paper_centre_nonneg c) I hE (by norm_num : (0 : ℝ) < 42 / 10000)
    (by norm_num) (by norm_num [mixtureFloor]) (by linarith)
  have hl := BstLean.Part252.latitude_mass_of_MASS (by omega) (paperDesignP n) c
    hw.1 hw.2.1 (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right (low_mass_price hn) hnR.le).trans
    (by rw [mul_div_cancel_left₀ _ hnR.ne']))

end BstLean.Part262
