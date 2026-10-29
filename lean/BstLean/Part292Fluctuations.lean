import BstLean.Part223CompleteSupply

/-! The order-24 and order-18 suppliers use one uniform set of normalized caps. -/
namespace BstLean.Part292
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170
open BstLean.Part223 BstLean.Part216

theorem k24_cap : k24 ≤ 3348/1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (24 : ℕ) ≠ 0) (by norm_num)
  rw [k24_pow]
  norm_num [Nat.factorial]

theorem energy_coefficient18_cap {n : ℕ} (hn : 8000 ≤ n) :
    energyCoefficient18 n ≤ (426/100 : ℝ)*n := by
  have h1 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 4233/2000 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have he := rpow_inv_natCast_pow (n := 18) (x := 2*((9 : ℕ).factorial : ℝ))
      (by positivity) (by norm_num)
    simp only [Nat.cast_ofNat] at he
    rw [he]
    norm_num [Nat.factorial]
  have h2 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 2112/269 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have he := rpow_inv_natCast_pow (n := 18) (x := 2*((18 : ℕ).factorial : ℝ))
      (by positivity) (by norm_num)
    simp only [Nat.cast_ofNat] at he
    rw [he]
    norm_num [Nat.factorial]
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have h := add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2*(n : ℝ)))
    (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 269/10))
  unfold energyCoefficient18 BstLean.Part202.beta
  nlinarith

theorem fluctuation_prices_band {n : ℕ} (hn : 8000 ≤ n)
    {L σ H Q : ℝ} (hL0 : 0 ≤ L) (hσ0 : 0 ≤ σ) (hH0 : 0 ≤ H) (hQ0 : 0 ≤ Q)
    (hL : (n : ℝ)*L ≤ 2025/1000) (hσ : sqrt (n : ℝ)*σ ≤ 2001/1000)
    (hH : H ≤ 533/1000) (hQ : Q ≤ 605/1000) :
    (k24 * (sqrt (n : ℝ)*L/2)*sqrt H)^24 ≤ (277/10000 : ℝ)^24 ∧
    (L*σ*energyCoefficient18 n)^18 * H^12 * Q^6 ≤ (1074/10000 : ℝ)^18 := by
  have hk0 := k24_nonneg
  have he0 := energyCoefficient18_nonneg n
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < sqrt (n : ℝ) := sqrt_pos.mpr hn0
  have hs : sqrt (n : ℝ)^2 = n := sq_sqrt hn0.le
  have hslo : (2236/25 : ℝ) ≤ sqrt (n : ℝ) := by
    apply le_sqrt_of_sq_le
    nlinarith
  have hLH : sqrt (n : ℝ)*L ≤ (2025/1000 : ℝ)/(2236/25) := by
    have he : sqrt (n : ℝ)*L = ((n : ℝ)*L)/sqrt (n : ℝ) := by
      apply (eq_div_iff hs0.ne').mpr
      nlinarith
    rw [he]
    exact div_le_div₀ (by norm_num) hL (by norm_num) hslo
  have hrootH : sqrt H ≤ 73007/100000 := by
    apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith
  have hloc : k24 * (sqrt (n : ℝ)*L/2)*sqrt H ≤ 277/10000 := by
    calc
      _ ≤ (3348/1000 : ℝ)*(((2025/1000)/(2236/25))/2)*(73007/100000) := by
        gcongr
        · exact k24_cap
      _ ≤ _ := by norm_num
  have hcoef := energy_coefficient18_cap hn
  have hE : L*σ*energyCoefficient18 n ≤
      (2025/1000 : ℝ)*(2001/1000)*(426/100)/(2236/25) := by
    have hprod : sqrt (n : ℝ)*(L*σ*energyCoefficient18 n) ≤
        (2025/1000 : ℝ)*(2001/1000)*(426/100) := by
      calc
        _ ≤ sqrt (n : ℝ)*(L*σ*((426/100 : ℝ)*n)) := by gcongr
        _ = ((n : ℝ)*L)*(sqrt (n : ℝ)*σ)*(426/100) := by ring
        _ ≤ _ := by gcongr
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2236/25)).mpr
    have he0 : 0 ≤ L*σ*energyCoefficient18 n :=
      mul_nonneg (mul_nonneg hL0 hσ0) (energyCoefficient18_nonneg n)
    nlinarith [mul_le_mul_of_nonneg_right hslo he0]
  constructor
  · exact pow_le_pow_left₀ (by positivity) hloc _
  · calc
      _ ≤ (((2025/1000 : ℝ)*(2001/1000)*(426/100)/(2236/25))^18)*
          (533/1000)^12*(605/1000)^6 := by gcongr
      _ ≤ _ := by norm_num

theorem originalFluctuations_band {n J : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (ν : Measure (Fin J)) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS c (node g)^2 ≤ 1) {O σ H Q : ℝ}
    (hO : 0 ≤ O) (hOp : OpB (A1 c) O)
    (hσ0 : 0 ≤ σ) (hH0 : 0 ≤ H) (hQ0 : 0 ≤ Q)
    (hL : (n : ℝ)*sqrt (tA n * (O^2/((n : ℝ)-2))) ≤ 2025/1000)
    (hσ : sqrt (n : ℝ)*σ ≤ 2001/1000)
    (hH : H ≤ 533/1000) (hQ : Q ≤ 605/1000)
    (hcap : ∀ g, 1-nodeS c (node g)^2 ≤ Q)
    (htrace : ∀ g, vsig2 c (nodeS c (node g)) ≤ σ^2*(1-nodeS c (node g)^2))
    (h12 : ∫⁻ g, ENNReal.ofReal ((1-nodeS c (node g)^2)^12) ∂ν ≤ ENNReal.ofReal (H^12)) :
    (∫⁻ g, ∫⁻ M, ENNReal.ofReal (|originalLocationFluct c (node g) M|^24)
      ∂gaussMat (mA n) (mA n) (tA n) ∂ν) ≤ ENNReal.ofReal ((277/10000 : ℝ)^24) ∧
    (∫⁻ g, ∫⁻ M, ENNReal.ofReal (|originalEnergyFluct c (node g) M|^18)
      ∂gaussMat (mA n) (mA n) (tA n) ∂ν) ≤ ENNReal.ofReal ((1074/10000 : ℝ)^18) := by
  have h := fluctuation_prices_band hn (sqrt_nonneg _) hσ0 hH0 hQ0 hL hσ hH hQ
  exact ⟨(originalLocationFluct_weighted24 (by omega) c ν node hs hO hOp hH0 h12).trans
      (ENNReal.ofReal_le_ofReal h.1),
    (originalEnergyFluct_weighted18 (by omega) c ν node hs hO hOp hσ0 hH0 hQ0
      hcap htrace h12).trans (ENNReal.ofReal_le_ofReal h.2)⟩

end BstLean.Part292

/-- info: 'BstLean.Part292.originalFluctuations_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.originalFluctuations_band
