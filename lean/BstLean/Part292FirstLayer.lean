import BstLean.Part292Rows
import BstLean.Part221FirstLayerEven
import BstLean.Part223Statistics

/-! The low-band first-layer moment at order 1664, before a table event
restricts the first matrix. The row radius bound covers every row. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part167 BstLean.Part168
open BstLean.Part212 BstLean.Part221

theorem active_moment1664_band {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    (hm : 0 < mA n) :
    (∫⁻ Z, ∫⁻ G, ENNReal.ofReal (activeRadius (d := n - 1 - 1) hm Z G ^ 1664)
      ∂Measure.pi (fun _ : Fin (mA n) => stdGauss (Fin (n - 1 - 1)))
      ∂Measure.pi (fun _ : Fin (mA n) => gaussianReal 0 1)) ≤
      ENNReal.ofReal (((11291 / 10000 : ℝ) * n) ^ 832) := by
  have hpt (Z : Fin (mA n) → ℝ) (G : Fin (mA n) → Fin (n - 1 - 1) → ℝ) :
      activeRadius hm Z G ≤ Mx hm G := by
    apply BstLean.Part217.activeMaximum_le hm (Mx_nonneg hm G)
    intro i _
    exact Finset.le_sup' (fun i => BstLean.Part53.radF53 (G i)) (Finset.mem_univ i)
  have h (Z : Fin (mA n) → ℝ) :=
    (lintegral_mono fun G => ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (BstLean.Part217.activeMaximum_nonneg hm _
        (fun i => sqrt_nonneg _)) (hpt Z G) 1664)).trans
      (show (∫⁻ G, ENNReal.ofReal (Mx hm G ^ 1664)
        ∂Measure.pi (fun _ : Fin (mA n) => stdGauss (Fin (n - 1 - 1)))) ≤
        ENNReal.ofReal (((11291 / 10000 : ℝ) * n) ^ 832) from by
          rw [show n - 1 - 1 = n - 2 by omega]
          exact maximum_moment1664_band hn hn' hm)
  exact (lintegral_mono h).trans_eq (by simp)

theorem first_layer_moment1664_band {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    {u w : Fin n → ℝ} {s cs : ℝ}
    (hu : normSq u = 1) (hw : normSq w = 1) (huw : ∑ i, u i * w i = 0)
    (hsc : s ^ 2 + cs ^ 2 = 1)
    (C : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (hC : ∀ A, normSq (C A) ≤ 1)
    (hCinv : ∀ W W' : Fin (mA n) → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ),
      (∀ i, (W i).1 = (W' i).1 ∧ (W i).2.1 = (W' i).2.1 ∧
        normSq (W i).2.2 = normSq (W' i).2.2) →
      C (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime (by omega) u w s cs) W) =
      C (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime (by omega) u w s cs) W')) :
    (∫⁻ A, ENNReal.ofReal (latSq (vecMul (C A) (D1A1 A (s • u + cs • w))) u w ^ 832)
      ∂gaussMat (mA n) n (2 / (n : ℝ))) ≤
      ENNReal.ofReal ((24933 / 10000 : ℝ) ^ 832) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := first_layer_active_even (j := 832) (by norm_num) (by omega : 4 ≤ n)
    (active_moment1664_band hn hn') hu hw huw hsc C hC hCinv
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have he : exactRadius (n - 1 - 1) 832 ^ 1664 * (2 / (n : ℝ)) ^ 832 *
      ((11291 / 10000 : ℝ) * n) ^ 832 =
      (exactRadius (n - 1 - 1) 832 ^ 2 * (2 * (11291 / 10000))) ^ 832 := by
    rw [show 1664 = 2 * 832 from rfl, pow_mul, ← mul_pow, ← mul_pow]
    congr 1
    field_simp
  rw [he]
  apply pow_le_pow_left₀ (by positivity)
  have hs := exactRadiusSquared1664_sharp hn
  nlinarith

theorem radialProduct_two (j : ℕ) : radialProduct 2 j = 2 ^ j * (j.factorial : ℝ) := by
  induction j with
  | zero => simp [radialProduct]
  | succ j ih =>
    rw [radialProduct_succ, ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, pow_succ]
    norm_num only [Nat.cast_ofNat]
    ring

/-- Arithmetic mean gives a deliberately coarse cap without a factorial certificate. -/
theorem gaussian_moment1664 : BstLean.Part152.gaussMomConst 832 ≤ 29 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (1664 : ℕ) ≠ 0) (by norm_num)
  rw [BstLean.Part152.gaussMomConst_pow (by norm_num : 1 ≤ (832 : ℕ))]
  rw [← radialProduct_two]
  calc
    radialProduct 2 832 ≤ ((2 : ℝ) + 831) ^ 832 := radialProduct832_le_mean (by norm_num)
    _ ≤ ((29 : ℝ) ^ 2) ^ 832 := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = _ := by rw [← pow_mul]

end BstLean.Part292

/-- info: 'BstLean.Part292.first_layer_moment1664_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.first_layer_moment1664_band
