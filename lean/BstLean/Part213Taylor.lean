import BstLean.Part186RA3

/-! The actual Taylor rows retain the radius polynomial before averaging.
The location proof removes the realized centre weights by Cauchy--Schwarz.
The energy proof retains the sum of the row majorants. -/
namespace BstLean.Part213
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (biasF biasW hB tA aLat bOfY)
open BstLean.Part153 (phiG phiG_pos)
open BstLean.Part137 (psiS)
open BstLean.Part186.RA
variable {n : ℕ}

/-- The exact radius polynomial supplies the location row-average bound. -/
theorem node_location_polynomial (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) {Smin Smax Dm Hm Vm Pm : ℝ} (hSm : 0 < Smin)
    (H : NodeStat c g Smin Smax Dm Hm Vm Pm) (ξ₁ ξ₂ : Fin (mA n) → ℝ)
    (hA0 : 0 ≤ AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA1 : 0 ≤ AF1 √Smin Dm Vm Pm (√(tA n) * O)) (hA2 : 0 ≤ AF2 √Smin Dm) :
    biasF c g ξ₁ ξ₂ ^ 8 ≤ (n : ℝ) ^ 4 * (∑ j, (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
      AF1 √Smin Dm Vm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j +
      AF2 √Smin Dm * rhoJ ξ₁ ξ₂ j ^ 2) ^ 2) ^ 4 := by
  set s := nodeS c g
  have hv : 0 < vsig2 c s := hSm.trans_le H.hS1
  rw [biasF_rows hn c g hs h1]
  set b := bOfY c (M0 c g ξ₁ ξ₂ *ᵥ hB c)
  set x : Fin (mA n) → ℝ := fun j => ∫ v, psiS (√(wT c g v)) ((M0 c g ξ₁ ξ₂ *ᵥ aLat c s v) j)
      ∂stdGauss (Fin (n - 1)) - psiS √(vsig2 c s) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j) with hx
  set P : Fin (mA n) → ℝ := fun j => AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
      AF1 √Smin Dm Vm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j + AF2 √Smin Dm * rhoJ ξ₁ ξ₂ j ^ 2 with hP
  have hxP : ∀ j, |x j| ≤ P j := by
    intro j
    have R := rowF (row_stat hn c g hs hO h1 hv ξ₁ ξ₂ j) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j)
    have e : ∀ v, (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j + ((M0 c g ξ₁ ξ₂ *ᵥ aLat c (nodeS c g) v) j -
        (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c (nodeS c g)) j) = (M0 c g ξ₁ ξ₂ *ᵥ aLat c s v) j := fun v => by
      simp only [s]; ring
    simp only [e] at R
    refine R.trans ?_
    have hρ : 0 ≤ rhoJ ξ₁ ξ₂ j := Real.sqrt_nonneg _
    have hC : 0 ≤ √(tA n) * O := mul_nonneg (Real.sqrt_nonneg _) hO
    have hsum := abs_add_abs_le (ξ₁ j) (ξ₂ j)
    refine TF_le (Real.sqrt_pos.mpr hSm) (Real.sqrt_le_sqrt H.hS1) hρ hC (by positivity) ?_
      (by have := vsig2_nonneg c s; have := tA_nonneg n; positivity) (by linarith [H.hS2])
      (mul_nonneg (by positivity) (DstN_nonneg c g)) ?_ (hUN_nonneg c g) H.hH (V2N_nonneg c g)
      H.hV (piN_nonneg c g) H.hP
    · have : (|ξ₁ j| + |ξ₂ j|) * (√(tA n) * O) ≤ √2 * rhoJ ξ₁ ξ₂ j * (√(tA n) * O) :=
        mul_le_mul_of_nonneg_right hsum hC
      unfold rhoJ at *
      nlinarith
    · rw [rhoJ_sq]
      exact mul_le_mul_of_nonneg_left H.hD (by positivity)
  have hκ : |(n : ℝ) / (√(n : ℝ) * √(normSq b)) * ∑ j, b j * x j| ≤ √(n : ℝ) * √(∑ j, x j ^ 2) := by
    rw [abs_mul]
    have h1' := BstLean.Part130.abs_dot_le b x
    have h2 := BstLean.Part170.kappa_b_le n b
    calc |(n : ℝ) / (√(n : ℝ) * √(normSq b))| * |∑ j, b j * x j|
        ≤ |(n : ℝ) / (√(n : ℝ) * √(normSq b))| * (√(normSq b) * √(normSq x)) := by gcongr
      _ = (|(n : ℝ) / (√(n : ℝ) * √(normSq b))| * √(normSq b)) * √(normSq x) := by ring
      _ ≤ √(n : ℝ) * √(normSq x) := by gcongr
      _ = √(n : ℝ) * √(∑ j, x j ^ 2) := rfl
  have hS0 : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have step1 : ((n : ℝ) / (√(n : ℝ) * √(normSq b)) * ∑ j, b j * x j) ^ 8 ≤
      (n : ℝ) ^ 4 * (∑ j, x j ^ 2) ^ 4 := by
    rw [← Even.pow_abs (by decide)]
    calc |(n : ℝ) / (√(n : ℝ) * √(normSq b)) * ∑ j, b j * x j| ^ 8
        ≤ (√(n : ℝ) * √(∑ j, x j ^ 2)) ^ 8 := pow_le_pow_left₀ (abs_nonneg _) hκ _
      _ = ((√(n : ℝ)) ^ 2) ^ 4 * ((√(∑ j, x j ^ 2)) ^ 2) ^ 4 := by ring
      _ = (n : ℝ) ^ 4 * (∑ j, x j ^ 2) ^ 4 := by
        rw [Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt hS0]

  have hsum : ∑ j, x j ^ 2 ≤ ∑ j, P j ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hxP j) 2
  calc
    _ ≤ (n : ℝ) ^ 4 * (∑ j, x j ^ 2) ^ 4 := step1
    _ ≤ (n : ℝ) ^ 4 * (∑ j, P j ^ 2) ^ 4 := by gcongr

/-- The exact radius polynomial supplies the energy row-average bound. -/
theorem node_energy_polynomial (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) {Smin Smax Dm Hm Vm Pm : ℝ} (hSm : 0 < Smin)
    (H : NodeStat c g Smin Smax Dm Hm Vm Pm) (ξ₁ ξ₂ : Fin (mA n) → ℝ)
    (hA1 : 0 ≤ AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)) :
    biasW c g ξ₁ ξ₂ ^ 8 ≤ (∑ j, (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
      AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j +
      AW2 Dm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j ^ 2)) ^ 8 := by
  set s := nodeS c g
  have hv : 0 < vsig2 c s := hSm.trans_le H.hS1
  rw [biasW_rows hn c g hs h1]
  set y : Fin (mA n) → ℝ := fun j => ∫ v, BstLean.Part170.G2 (√(wT c g v))
      ((M0 c g ξ₁ ξ₂ *ᵥ aLat c s v) j) ∂stdGauss (Fin (n - 1)) -
        BstLean.Part170.G2 √(vsig2 c s) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j) with hy
  set Q : Fin (mA n) → ℝ := fun j => AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
      AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j +
      AW2 Dm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j ^ 2 with hQ
  have hyQ : ∀ j, |y j| ≤ Q j := by
    intro j
    have R := rowW (row_stat hn c g hs hO h1 hv ξ₁ ξ₂ j) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j)
    have e : ∀ v, (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j + ((M0 c g ξ₁ ξ₂ *ᵥ aLat c (nodeS c g) v) j -
        (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c (nodeS c g)) j) = (M0 c g ξ₁ ξ₂ *ᵥ aLat c s v) j := fun v => by
      simp only [s]; ring
    simp only [e] at R
    refine R.trans ?_
    have hρ : 0 ≤ rhoJ ξ₁ ξ₂ j := Real.sqrt_nonneg _
    have hC : 0 ≤ √(tA n) * O := mul_nonneg (Real.sqrt_nonneg _) hO
    have hsum := abs_add_abs_le (ξ₁ j) (ξ₂ j)
    have hsum' : (|ξ₁ j| + |ξ₂ j|) * (√(tA n) * O) ≤ √2 * rhoJ ξ₁ ξ₂ j * (√(tA n) * O) :=
      mul_le_mul_of_nonneg_right hsum hC
    refine TW_le (Real.sqrt_pos.mpr hSm) (Real.sqrt_le_sqrt H.hS1) (Real.sqrt_le_sqrt H.hS2) hρ hC
      ?_ (by positivity) ?_
      (by have := vsig2_nonneg c s; have := tA_nonneg n; positivity) (by linarith [H.hS2])
      (mul_nonneg (by positivity) (DstN_nonneg c g)) ?_ (hUN_nonneg c g) H.hH (V2N_nonneg c g)
      H.hV (piN_nonneg c g) H.hP
    · have := abs_M0abar_le hn c g hs hO h1 ξ₁ ξ₂ j
      unfold rhoJ at *
      nlinarith
    · unfold rhoJ at *
      nlinarith
    · rw [rhoJ_sq]
      exact mul_le_mul_of_nonneg_left H.hD (by positivity)
  have hS : |∑ j, y j| ≤ ∑ j, |y j| := Finset.abs_sum_le_sum_abs _ _

  have hS2 : ∑ j, |y j| ≤ ∑ j, Q j := Finset.sum_le_sum fun j _ => hyQ j
  calc
    (∑ j, y j) ^ 8 = |∑ j, y j| ^ 8 := (Even.pow_abs (by decide : Even 8) _).symm
    _ ≤ (∑ j, Q j) ^ 8 := pow_le_pow_left₀ (abs_nonneg _) (hS.trans hS2) 8

#print axioms node_location_polynomial
#print axioms node_energy_polynomial
end BstLean.Part213

