import BstLean.Part180HQFl
import BstLean.Part252Scalar

/-! Rational enclosures for the HQ fluctuation price at dimension 12225. -/
namespace BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 17 / 10
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 402 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1935 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 191 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 132 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 234 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 163 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12225 L ε Exp A D e4 d4 e6 d6 ≤ 12 / 10 ^ 6 := by
  have hκ := h.kappa
  have hL := h.location
  have hε := h.epsilon
  have hX := h.exponential
  have hA := h.energy
  have hD := h.displacement
  have he4 := h.energy_four
  have hd4 := h.location_four
  have he6 := h.energy_six
  have hd6 := h.location_six
  have hκ0 := hκ.1
  have hκ1 := hκ.2
  have hL0 := hL.1
  have hL1 := hL.2
  have hε0 := hε.1
  have hε1 := hε.2
  have hX0 := hX.1
  have hX1 := hX.2
  have hA0 := hA.1
  have hA1 := hA.2
  have hD0 := hD.1
  have hD1 := hD.2
  have he40 := he4.1
  have he41 := he4.2
  have hd40 := hd4.1
  have hd41 := hd4.2
  have he60 := he6.1
  have he61 := he6.2
  have hd60 := hd6.1
  have hd61 := hd6.2
  have hs : √(A * D) ≤ 28 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12225 * A / 2 + D + L * √(A * D)) ≤ 445 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12225 * (402 / 10 ^ 9) / 2 +
          1935 / 10 ^ 6 + (17 / 10) * (28 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12225 L e4 d4 ≤ 402 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12225 / 2 * (191 / 10 ^ 5) ^ 2 +
          (132 / 1000) ^ 2 + (17 / 10) * (132 / 1000) * (191 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12225 L e6 d6 ≤ 608 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12225 / 2 * (234 / 10 ^ 5) ^ 2 +
          (163 / 1000) ^ 2 + (17 / 10) * (163 / 1000) * (234 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12225 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12225 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12225 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12225 * (402 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (402 / 10 ^ 9) * (1935 / 10 ^ 6)) +
      (445 / 100000) ^ 2 / 2 + (445 / 100000) * (402 / 10000) ^ 2 / 6 +
      (402 / 10000) ^ 4 / 24 + (402 / 10000) ^ 2 * (608 / 10000) ^ 3 / 120 +
      2187 * (608 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12225 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 12 / 10 ^ 7 := by
  have hε := h.epsilon
  have hA := h.energy
  have hD := h.displacement
  have he6 := h.energy_six
  have hd6 := h.location_six
  have hε0 := hε.1
  have hε1 := hε.2
  have hA0 := hA.1
  have hA1 := hA.2
  have hD0 := hD.1
  have hD1 := hD.2
  have he60 := he6.1
  have he61 := he6.2
  have hd60 := hd6.1
  have hd61 := hd6.2
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 635 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 44 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12225 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((402 / 10 ^ 9) * (635 / 10 ^ 6) * (234 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1935 / 10 ^ 6) * (44 / 1000) * (163 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12225 * (402 / 10 ^ 9) ^ 2 + 2 * (402 / 10 ^ 9) * (1935 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12225 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12225 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 1975 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part252
