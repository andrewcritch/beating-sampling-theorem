import BstLean.Part242HQPass
import BstLean.Part242MixtureConstants

/-! SY2 changes the integrated quadratic terms and keeps the higher pointwise prices. -/
namespace BstLean.Part242
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part130 (normSq)
open BstLean.Part157 BstLean.Part161 BstLean.Part162
open BstLean.Part29 (stdGauss)

variable {n : ℕ}

theorem chi_price_SY2 (D : Design n) (c : Ret n) (split : SplitData n)
    {ε δ L slow A Dm e4 d4 e6 d6 : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hslow : 0 < slow) (hcA : 0 < normSq c.2.1.2)
    (hwin : ∀ a ∈ keptIx D c split, slow ≤ split.S0 a ∧ ∀ v ∈ slice split a,
      |sA D c a v / split.S0 a - 1| ≤ ε ∧ |lA D c a v - split.lam0 a| ≤ δ ∧
      normSq c.2.1.2 / split.S0 a * (lA D c a v - split.lam0 a) ^ 2 ≤ L ^ 2)
    (hcent : ∀ a ∈ keptIx D c split,
      (∫ v in slice split a, (lA D c a v - split.lam0 a) ∂stdGauss (Fin (n - 1))) = 0 ∧
      (∫ v in slice split a, (sA D c a v / split.S0 a - 1) ∂stdGauss (Fin (n - 1))) = 0)
    (hv : LBound ((muI n).restrict (keptIx D c split)) 3 (condMom split (epsF D c split) 2) A)
    (hw : LBound ((muI n).restrict (keptIx D c split)) 3 (condMom split (delF D c split) 2) Dm)
    (he4 : 0 ≤ e4) (hd4 : 0 ≤ d4) (he6 : 0 ≤ e6) (hd6 : 0 ≤ d6)
    (Ie4 : ∫ a in keptIx D c split, condMom split (epsF D c split) 8 a ∂muI n ≤ e4 ^ 8)
    (Id4 : ∫ a in keptIx D c split, condMom split (delF D c split) 8 a ∂muI n ≤ d4 ^ 8)
    (Ie6 : ∫ a in keptIx D c split, condMom split (epsF D c split) 12 a ∂muI n ≤ e6 ^ 12)
    (Id6 : ∫ a in keptIx D c split, condMom split (delF D c split) 12 a ∂muI n ≤ d6 ^ 12) :
    ∫ a in keptIx D c split, chiK D c split a ∂muI n ≤
      priceC (1 - ε ^ 2)⁻¹ n L ε
        (exp ((1 - ε ^ 2)⁻¹ * (n * ε ^ 2 / 2 + L ^ 2 * (1 + ε)))) A Dm e4 d4 e6 d6 := by
  have hm : ((muI n).restrict (keptIx D c split)) univ ≤ 1 :=
    (Measure.restrict_le_self univ).trans (by simp)
  have hv2 := hv.lower (by norm_num) (by norm_num) (by norm_num : (2 : ℝ≥0∞) ≤ 3) hm
  have hw2 := hw.lower (by norm_num) (by norm_num) (by norm_num : (2 : ℝ≥0∞) ≤ 3) hm
  exact BstLean.Part180.int_chiK_le D c split hε0 hε1 hδ hL hslow hcA hwin hcent
    hv.nonneg hw.nonneg he4 hd4 he6 hd6 hv2.squareIntegral.2 hw2.squareIntegral.2 Ie4 Id4 Ie6 Id6

instance holder2_2 : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]

theorem removal_L2 {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {β : X → ℝ} (mβ : Measurable β) (hβ0 : ∀ x, 0 ≤ β x) (hβ1 : ∀ x, β x ≤ 1)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∫ x, β x ∂μ ≤ B) :
    LBound μ 2 β (sqrt B) := by
  have iβ := BstLean.Part162.intB (μ := μ) mβ
    (fun x => by simpa only [abs_of_nonneg (hβ0 x)] using hβ1 x)
  have iβ2 := BstLean.Part162.intB (μ := μ) (mβ.pow_const 2) (M := 1) (fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hβ0 x, hβ1 x])
  have bβ2 : ∫ x, β x ^ 2 ∂μ ≤ B :=
    (integral_mono iβ2 iβ (fun x => by nlinarith [hβ0 x, hβ1 x])).trans hB
  apply LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
  refine ⟨mβ, sqrt_nonneg B, ?_⟩
  simp only [sq_abs]
  rw [sq_sqrt hB0, ← ofReal_integral_eq_lintegral_ofReal iβ2
    (Filter.Eventually.of_forall fun x => sq_nonneg (β x))]
  exact ENNReal.ofReal_le_ofReal bβ2

/-- The displacement location price uses the same removal allowance once. -/
theorem displacement_location_SY2 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (K : Set X)
    (n : ℕ) {χ Γ V η B : ℝ} (hχ : 0 ≤ χ) (hη : η < 1) (hB0 : 0 ≤ B)
    {β v R : X → ℝ} (mβ : Measurable β) (hβ0 : ∀ x, 0 ≤ β x) (hβ1 : ∀ x, β x ≤ 1)
    (hB : ∫ x, β x ∂μ ≤ B)
    (hv : LBound (μ.restrict K) 4 v V) (hR : LBound (μ.restrict K) 4 R Γ) :
    ∫ x in K, |((n : ℝ) * χ / (1 - η)) * (β x * (v x * R x))| ∂μ ≤
      mixD n χ Γ V η * sqrt B := by
  have hβ := (removal_L2 μ mβ hβ0 hβ1 hB0 hB).restrict K
  have hvr : LBound (μ.restrict K) 2 (fun x => v x * R x) (V * Γ) := hv.mul hR
  have hp : LBound (μ.restrict K) 1 (fun x => β x * (v x * R x)) (sqrt B * (V * Γ)) :=
    hβ.mul hvr
  have ha : 0 ≤ (n : ℝ) * χ / (1 - η) := by positivity
  have hi := hp.integralAbs
  simp only [abs_mul, abs_of_nonneg ha]
  rw [integral_const_mul]
  have he : ((n : ℝ) * χ / (1 - η)) * (sqrt B * (V * Γ)) =
      mixD n χ Γ V η * sqrt B := by unfold mixD; ring
  simpa only [abs_mul] using (mul_le_mul_of_nonneg_left hi.2 ha).trans_eq he

end BstLean.Part242
