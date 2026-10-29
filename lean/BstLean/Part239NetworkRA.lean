import BstLean.Part239RA
import BstLean.Part213NetworkRA

/-! The actual conditional network biases use order104 and the exact correction. -/
namespace BstLean.Part239
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (biasF biasW tA)
open BstLean.Part213
open BstLean.Part223 (MomentBound)
open BstLean.Part186.RA (ρ2)
variable {n : ℕ}

lemma sum_eq_mul_average {X : Type*} {m : ℕ} (hm : 1 ≤ m) (f : X → ℝ) (y : Fin m → X) :
    ∑ j, f (y j) = (m : ℝ) * iidAverage m f y := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold iidAverage
  rw [← mul_assoc, mul_inv_cancel₀ hm0, one_mul]

theorem conditional_location_RA104_exact (hn : 1 ≤ n) (c : Ret n) (g : ℕ)
    (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O) (h1 : OpB (A1 c) O)
    {Smin Smax Dm Hm Vm Pm : ℝ} (hSm : 0 < Smin)
    (H : NodeStat c g Smin Smax Dm Hm Vm Pm)
    (hA0 : 0 ≤ AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA1 : 0 ≤ AF1 √Smin Dm Vm Pm (√(tA n) * O)) (hA2 : 0 ≤ AF2 √Smin Dm)
    {AQ : ℝ}
    (hM : MomentBound ρ2 104
      (radiusPolynomial (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
        (AF1 √Smin Dm Vm Pm (√(tA n) * O)) (AF2 √Smin Dm)) AQ) :
    ∫⁻ y, ENNReal.ofReal (biasF c g (fun j => (y j).1) (fun j => (y j).2) ^ 104)
      ∂(Measure.pi fun _ : Fin (mA n) => ρ2) ≤
      ENNReal.ofReal ((n : ℝ) ^ 52 * (mA n : ℝ) ^ 52 *
        (collectedSecond (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
          (AF1 √Smin Dm Vm Pm (√(tA n) * O)) (AF2 √Smin Dm) +
          exactCorrection 52 (mA n) * AQ ^ 2) ^ 52) := by
  let a0 := AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm
  let a1 := AF1 √Smin Dm Vm Pm (√(tA n) * O)
  let a2 := AF2 √Smin Dm
  let β := radiusPolynomial a0 a1 a2
  have hm : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ hn
  have hMβ : MomentBound ρ2 104 β AQ := hM
  have havg := location_RA_from_top (m := mA n) (p := 26) ρ2 hm (by norm_num) hMβ
  have hmean : ∫ p, β p ^ 2 ∂ρ2 = collectedSecond a0 a1 a2 :=
    (radius_polynomial_second a0 a1 a2).2
  have hB0 : 0 ≤ (∫ p, β p ^ 2 ∂ρ2) + exactCorrection 52 (mA n) * AQ ^ 2 := by
    exact add_nonneg (integral_nonneg fun _ => sq_nonneg _)
      (mul_nonneg (exactCorrection_nonneg _ _) (sq_nonneg _))
  have hnonneg : ∀ y, 0 ≤ iidAverage (mA n) (fun x => β x ^ 2) y := by
    intro y
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hmoment := havg.moment
  have hroot (x : ℝ) (hx : 0 ≤ x) : sqrt x ^ (4 * 26) = x ^ 52 := by
    change sqrt x ^ (2 * 52) = x ^ 52
    rw [pow_mul, sq_sqrt hx]
  simp only [abs_of_nonneg (sqrt_nonneg _), hroot _ (hnonneg _), hroot _ hB0] at hmoment
  rw [hmean] at hmoment
  have hpoint : ∀ y : Fin (mA n) → ℝ × ℝ,
      biasF c g (fun j => (y j).1) (fun j => (y j).2) ^ 104 ≤
        (n : ℝ) ^ 52 * (∑ j, β (y j) ^ 2) ^ 52 := by
    intro y
    have h := node_location_polynomial hn c g hs hO h1 hSm H
      (fun j => (y j).1) (fun j => (y j).2) hA0 hA1 hA2
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
      biasF c g (fun j => (y j).1) (fun j => (y j).2) ^ 8) h 13
    convert hh using 1 <;>
      (try simp only [β, radiusPolynomial, planeRadius, BstLean.Part186.RA.RR,
        BstLean.Part171.rhoJ, a0, a1, a2]) <;> ring
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal ((n : ℝ) ^ 52 * (mA n : ℝ) ^ 52) *
        ENNReal.ofReal (iidAverage (mA n) (fun x => β x ^ 2) y ^ 52)
          ∂(Measure.pi fun _ : Fin (mA n) => ρ2) := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      refine (hpoint y).trans_eq ?_
      rw [sum_eq_mul_average hm (fun x => β x ^ 2) y, mul_pow]
      ring
    _ = ENNReal.ofReal ((n : ℝ) ^ 52 * (mA n : ℝ) ^ 52) * ∫⁻ y,
        ENNReal.ofReal (iidAverage (mA n) (fun x => β x ^ 2) y ^ 52)
          ∂(Measure.pi fun _ : Fin (mA n) => ρ2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ 52 * (mA n : ℝ) ^ 52) *
        ENNReal.ofReal ((collectedSecond a0 a1 a2 + exactCorrection 52 (mA n) * AQ ^ 2) ^ 52) :=
      mul_le_mul' le_rfl hmoment
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

theorem conditional_energy_RA104_exact (hn : 1 ≤ n) (c : Ret n) (g : ℕ)
    (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O) (h1 : OpB (A1 c) O)
    {Smin Smax Dm Hm Vm Pm : ℝ} (hSm : 0 < Smin)
    (H : NodeStat c g Smin Smax Dm Hm Vm Pm)
    (hA0 : 0 ≤ AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA1 : 0 ≤ AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O))
    (hA2 : 0 ≤ AW2 Dm Pm (√(tA n) * O)) {AQ : ℝ}
    (hM : MomentBound ρ2 104
      (radiusPolynomial (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
        (AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)) (AW2 Dm Pm (√(tA n) * O))) AQ) :
    ∫⁻ y, ENNReal.ofReal (biasW c g (fun j => (y j).1) (fun j => (y j).2) ^ 104)
      ∂(Measure.pi fun _ : Fin (mA n) => ρ2) ≤
      ENNReal.ofReal ((mA n : ℝ) ^ 104 *
        (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
          AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O) * sqrt (π / 2) +
          2 * AW2 Dm Pm (√(tA n) * O) + exactCorrection 104 (mA n) * AQ) ^ 104) := by
  let a0 := AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm
  let a1 := AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)
  let a2 := AW2 Dm Pm (√(tA n) * O)
  let β := radiusPolynomial a0 a1 a2
  have hm : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ hn
  have hβ0 : ∀ p, 0 ≤ β p := by
    intro p
    dsimp [β, radiusPolynomial]
    have hR := sqrt_nonneg (BstLean.Part186.RA.RR p)
    positivity
  have hMβ : MomentBound ρ2 104 β AQ := hM
  have havg := energy_RA_from_top (m := mA n) (p := 52) ρ2 hm (by norm_num) hβ0 hMβ
  have hmean : ∫ p, β p ∂ρ2 = a0 + a1 * sqrt (π / 2) + 2 * a2 :=
    (radius_polynomial_mean a0 a1 a2).2
  have hnonneg : ∀ y, 0 ≤ iidAverage (mA n) β y := by
    intro y
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun j _ => hβ0 _)
  have hmoment := havg.moment
  simp only [abs_of_nonneg (hnonneg _), hmean] at hmoment
  have hpoint : ∀ y : Fin (mA n) → ℝ × ℝ,
      biasW c g (fun j => (y j).1) (fun j => (y j).2) ^ 104 ≤ (∑ j, β (y j)) ^ 104 := by
    intro y
    have h := node_energy_polynomial hn c g hs hO h1 hSm H
      (fun j => (y j).1) (fun j => (y j).2) hA1
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
      biasW c g (fun j => (y j).1) (fun j => (y j).2) ^ 8) h 13
    convert hh using 1 <;>
      (try simp only [β, radiusPolynomial, planeRadius, BstLean.Part186.RA.RR,
        BstLean.Part171.rhoJ, a0, a1, a2]) <;> ring
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal ((mA n : ℝ) ^ 104) * ENNReal.ofReal
        (iidAverage (mA n) β y ^ 104) ∂(Measure.pi fun _ : Fin (mA n) => ρ2) := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      refine (hpoint y).trans_eq ?_
      rw [sum_eq_mul_average hm β y, mul_pow]
    _ = ENNReal.ofReal ((mA n : ℝ) ^ 104) * ∫⁻ y, ENNReal.ofReal
        (iidAverage (mA n) β y ^ 104) ∂(Measure.pi fun _ : Fin (mA n) => ρ2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((mA n : ℝ) ^ 104) * ENNReal.ofReal
        ((a0 + a1 * sqrt (π / 2) + 2 * a2 + exactCorrection 104 (mA n) * AQ) ^ 104) :=
      mul_le_mul' le_rfl hmoment
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

#print axioms conditional_location_RA104_exact
#print axioms conditional_energy_RA104_exact
end BstLean.Part239
