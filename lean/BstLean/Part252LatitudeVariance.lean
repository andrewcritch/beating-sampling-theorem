import BstLean.Part212Fields
import BstLean.Part242ZNetwork

/-! The order-twelve tangent certificate controls the order-twelve latitude variance. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part242
open BstLean.Part53 (unitF53)
open BstLean.Part148 (EuLip)

noncomputable def latitudeVariance {n : ℕ} (D : Design n) (c : Ret n)
    (Φ : (Fin n → ℝ) → ℝ) (a : Ix n) : ℝ :=
  conditionalVariance (stdGauss (Fin (n - 1)))
    (fun v => Φ (xLat c (latC D c a) (unitF53 v)))

theorem measurable_latitudeVariance {n : ℕ} (D : Design n) (c : Ret n)
    {Φ : (Fin n → ℝ) → ℝ} (hΦ : Measurable Φ) :
    Measurable (latitudeVariance D c Φ) := by
  have hX := hΦ.comp (measurable_xA D c)
  have hE := measurable_latitudeMean (stdGauss (Fin (n - 1))) hX
  exact measurable_latitudeMean (stdGauss (Fin (n - 1)))
    ((hX.sub (hE.comp measurable_fst)).pow_const 2)

theorem latitudeVariance_nonneg {n : ℕ} (D : Design n) (c : Ret n)
    (Φ : (Fin n → ℝ) → ℝ) (a : Ix n) : 0 ≤ latitudeVariance D c Φ a :=
  integral_nonneg fun v => sq_nonneg _

theorem latitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (D : Design n) (c : Ret n)
    {Φ : (Fin n → ℝ) → ℝ} {L C : ℝ} (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ t x, 0 < t → Φ (t • x) = t * Φ x) (hC : 0 ≤ C)
    (h12 : ∫ a, ∫ v, psiA Φ D c a v ^ 12 ∂stdGauss (Fin (n - 1))
      ∂muI n ≤ (C / n) ^ 12) :
    LBound (muI n) 12 (latitudeVariance D c Φ) (C / n / ((n : ℝ) - 2)) := by
  let ν := stdGauss (Fin (n - 1))
  let μ := (muI n).prod ν
  let ψ : Ix n × (Fin (n - 1) → ℝ) → ℝ := fun p => psiA Φ D c p.1 p.2
  have hb := psiA_bounds (by omega) D c hL0 hL hhom
  have mψ : Measurable ψ := measurable_psiA (hL.continuous hL0) D c
  have iψ : Integrable (fun p => ψ p ^ 12) μ :=
    Integrable.of_bound (mψ.pow_const 12).aestronglyMeasurable ((2 * L ^ 2) ^ 12)
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hb p.1 p.2).1 12)]
        exact pow_le_pow_left₀ (hb p.1 p.2).1 (hb p.1 p.2).2 12)
  have hp : BstLean.Part223.MomentBound μ 12 ψ (C / n) := by
    refine ⟨mψ, div_nonneg hC (Nat.cast_nonneg n), ?_⟩
    simp only [(by decide : Even 12).pow_abs]
    rw [← ofReal_integral_eq_lintegral_ofReal iψ
      (Filter.Eventually.of_forall fun p => pow_nonneg (hb p.1 p.2).1 12)]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_prod _ iψ]
    exact h12
  have hm := conditional_moment (muI n) ν (by decide : Even 12) hp
    (fun a v => by rw [abs_of_nonneg (hb a v).1]; exact (hb a v).2)
  have hd : 0 < (n : ℝ) - 2 := by
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hscaled := (LBound.ofMoment (by norm_num : (12 : ℕ) ≠ 0) hm).scale
    (by norm_num : (12 : ℕ) ≠ 0) (inv_nonneg.mpr hd.le)
  have he : ((n : ℝ) - 2)⁻¹ * (C / n) = C / n / ((n : ℝ) - 2) := by ring
  rw [he] at hscaled
  apply hscaled.mono (measurable_latitudeVariance D c (hL.continuous hL0).measurable)
  apply Filter.Eventually.of_forall
  intro a
  have hR0 : 0 ≤ ((n : ℝ) - 2)⁻¹ * latitudeMean ν ψ a :=
    mul_nonneg (inv_nonneg.mpr hd.le) (integral_nonneg fun v => (hb a v).1)
  rw [abs_of_nonneg (latitudeVariance_nonneg D c Φ a), abs_of_nonneg hR0]
  simpa only [latitudeVariance, conditionalVariance, latitudeMean, ψ, ν,
    div_eq_mul_inv, mul_comm] using idx_var_psi hn D c hL0 hL hhom a

theorem conditionalVariance_scale {V : Type*} [MeasurableSpace V]
    (ν : Measure V) (f : V → ℝ) (a : ℝ) :
    conditionalVariance ν (fun v => a * f v) = a ^ 2 * conditionalVariance ν f := by
  unfold conditionalVariance
  rw [integral_const_mul]
  simp_rw [← mul_sub, mul_pow]
  exact integral_const_mul _ _

theorem lambda_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (D : Design n)
    (hD : AgentCentre154 D) (c : Ret n) {C : ℝ} (hC : 0 ≤ C)
    (he : 0 < normSq (D.bA c.1 c.2.1.1) / n)
    (hk : BstLean.Part160.agKey D c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12 (latitudeVariance D c (lamX D c))
      ((C / (normSq (D.bA c.1 c.2.1.1) / n)) / n / ((n : ℝ) - 2)) := by
  apply latitude_variance_norm12 hn D c (lipLam_nonneg D c) (lamX_euLip D c)
    (fun t x ht => lamX_hom D c t x ht) (div_nonneg hC he.le)
  have hh := BstLean.Part212.fresh_lambda_certificate (by omega) D hD c
    (div_nonneg hC (Nat.cast_nonneg n)) he hk
  convert hh using 1 <;> congr 1 <;> ring

theorem residual_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (D : Design n)
    (hD : AgentCentre154 D) (c : Ret n) {C : ℝ} (hC : 0 ≤ C)
    (hk : BstLean.Part160.agKey D c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12 (latitudeVariance D c (sigX D c))
      ((2 * C / n) / n / ((n : ℝ) - 2)) := by
  apply latitude_variance_norm12 hn D c (lipSig_nonneg D c) (sigX_euLip D c)
    (fun t x ht => sigX_hom D c t x ht) (by positivity)
  have hh := BstLean.Part212.fresh_residual_certificate (by omega) D hD c
    (div_nonneg hC (Nat.cast_nonneg n)) hk
  convert hh using 1 <;> congr 1 <;> ring

end BstLean.Part252
