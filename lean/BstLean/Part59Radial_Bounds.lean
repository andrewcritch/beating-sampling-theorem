import BstLean.Part59Radial_Angular
import BstLean.Part59Radial_Moments
import BstLean.Part36Index

/-! # Part 59: radial independence and dimension estimates -/

namespace BstLean.Part59

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD unitOfD)
open BstLean.Part53 (GaussPolar53)
open BstLean.Part53.T2Aux

variable {n d : ℕ}

lemma radial_product59x (hP : GaussPolar53) (r : ℕ)
    (G : (CoefIdxD n d → ℝ) → ℝ) (hG : Measurable G) (_hG0 : ∀ W, 0 ≤ G W)
    (hi : Integrable (fun Z => (lam59 n d Z - 1) ^ (2 * r)) (stdGauss (CoefIdxD n d))) :
    (∫⁻ Z, ENNReal.ofReal ((lam59 n d Z - 1) ^ (2 * r) * G (unitOfD Z))
      ∂stdGauss (CoefIdxD n d)) =
      ENNReal.ofReal (∫ Z, (lam59 n d Z - 1) ^ (2 * r) ∂stdGauss (CoefIdxD n d)) *
        ∫⁻ Z, ENNReal.ofReal (G (unitOfD Z)) ∂stdGauss (CoefIdxD n d) := by
  let a := fun t : ℝ => ENNReal.ofReal ((t / Real.sqrt (DD n d) - 1) ^ (2 * r))
  have ha : Measurable a := by dsimp [a]; fun_prop
  have hp := polar_product hP a (fun W => ENNReal.ofReal (G W)) ha hG.ennreal_ofReal
  have hnn (Z : CoefIdxD n d → ℝ) : 0 ≤ (lam59 n d Z - 1) ^ (2 * r) := by
    rw [pow_mul]; positivity
  simp_rw [ENNReal.ofReal_mul (hnn _)]
  change (∫⁻ Z, ENNReal.ofReal ((lam59 n d Z - 1) ^ (2 * r)) *
      ENNReal.ofReal (G (unitOfD Z)) ∂stdGauss (CoefIdxD n d)) =
      (∫⁻ Z, ENNReal.ofReal ((lam59 n d Z - 1) ^ (2 * r)) ∂stdGauss (CoefIdxD n d)) *
        ∫⁻ Z, ENNReal.ofReal (G (unitOfD Z)) ∂stdGauss (CoefIdxD n d) at hp
  rw [hp]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn)]

lemma radial_dimension59x (hd : 1 ≤ d) (_hn : 1 ≤ n) :
    (n : ℝ) ^ 2 ≤ DD n d ∧ n + 1 ≤ (n + d).choose d := by
  have hc : n + 1 ≤ (n + d).choose d := by
    rw [← Nat.choose_symm_add]
    calc
      n + 1 = (n + 1).choose n := by rw [Nat.choose_succ_self_right]
      _ ≤ (n + d).choose n := Nat.choose_le_choose n (by omega)
  refine ⟨?_, hc⟩
  rw [BstLean.Part36.DD_eq]
  have hcr : (n : ℝ) + 1 ≤ ((n + d).choose d : ℝ) := by exact_mod_cast hc
  nlinarith [show (0 : ℝ) ≤ n by positivity]

lemma radial_dimension_ratio59x (hd : 1 ≤ d) (hn : 1 ≤ n) (r : ℕ) (hr : 1 ≤ r) :
    (n : ℝ) ^ r / DD n d ^ r ≤ 1 / n := by
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbound := (radial_dimension59x hd hn).1
  have hnn : 0 ≤ (n : ℝ) / DD n d := div_nonneg hnR.le hD.le
  have hle : (n : ℝ) / DD n d ≤ 1 := by
    rw [div_le_iff₀ hD]; nlinarith
  have hrpow : ((n : ℝ) / DD n d) ^ r ≤ (n : ℝ) / DD n d := by
    simpa using pow_le_pow_of_le_one hnn hle hr
  rw [← div_pow]
  apply hrpow.trans
  rw [div_le_div_iff₀ hD hnR]
  nlinarith

lemma radial_card59x (hd : 1 ≤ d) (hn : 40 ≤ n) :
    1000 ≤ Fintype.card (CoefIdxD n d) := by
  rw [BstLean.Part36.card_coefIdxD]
  have hc := (radial_dimension59x hd (by omega : 1 ≤ n)).2
  nlinarith

end BstLean.Part59
