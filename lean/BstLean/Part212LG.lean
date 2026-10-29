import BstLean.Part162LGs
import BstLean.Part212Event
import BstLean.Part195Rotation

/-! Realized latitude consequences with a variable certificate constant. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part157 BstLean.Part161 BstLean.Part162
open BstLean.Part148 (EuLip)
open BstLean.Part53 (unitF53)

theorem young_lower {x T : ℝ} (hx : 0 ≤ x) (hT : 0 < T)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    x ^ q ≤ (q / (12 : ℝ) / T ^ (12 - q)) * x ^ 12 +
      (1 - q / (12 : ℝ)) * T ^ q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq12
  set w : ℝ := q / 12
  have hw0 : 0 ≤ w := by positivity
  have hw1 : 0 ≤ 1 - w := by dsimp [w]; linarith
  have key := Real.geom_mean_le_arith_mean2_weighted hw0 hw1
    (pow_nonneg hx 12) (pow_nonneg hT.le 12) (by ring)
  have e1 : (x ^ 12) ^ w = x ^ q := by
    rw [← Real.rpow_natCast x 12, ← Real.rpow_mul hx]
    norm_num only [Nat.cast_ofNat]
    have he : (12 : ℝ) * w = q := by dsimp [w]; ring
    rw [he, Real.rpow_natCast]
  have e2 : (T ^ 12) ^ (1 - w) = T ^ (12 - q) := by
    rw [← Real.rpow_natCast T 12, ← Real.rpow_mul hT.le]
    norm_num only [Nat.cast_ofNat]
    have he : (12 : ℝ) * (1 - w) = (12 - q : ℕ) := by
      rw [Nat.cast_sub hq12]; dsimp [w]; push_cast; ring
    rw [he, Real.rpow_natCast]
  rw [e1, e2] at key
  have hp : T ^ 12 = T ^ (12 - q) * T ^ q := by
    rw [← pow_add, Nat.sub_add_cancel hq12]
  have hpos : 0 < T ^ (12 - q) := pow_pos hT _
  rw [hp] at key
  calc x ^ q ≤ (w * x ^ 12 + (1 - w) * (T ^ (12 - q) * T ^ q)) /
      T ^ (12 - q) := (le_div_iff₀ hpos).mpr key
    _ = _ := by dsimp [w]; field_simp <;> ring

/-- Lyapunov for all positive integer orders up to twelve. -/
theorem moment_lower12 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {g : Ω → ℝ} (hg : Measurable g) (h0 : ∀ x, 0 ≤ g x)
    (hi : ∀ k : ℕ, Integrable (fun x => g x ^ k) μ)
    {T : ℝ} (hT : 0 < T) (h12 : ∫ x, g x ^ 12 ∂μ ≤ T ^ 12)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ x, g x ^ q ∂μ ≤ T ^ q := by
  let a : ℝ := q / (12 : ℝ) / T ^ (12 - q)
  let b : ℝ := (1 - q / (12 : ℝ)) * T ^ q
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h := integral_mono (hi q) (((hi 12).const_mul a).add (integrable_const b))
    (fun x => young_lower (h0 x) hT hq hq12)
  change (∫ x, g x ^ q ∂μ) ≤ ∫ x, a * g x ^ 12 + b ∂μ at h
  rw [integral_add ((hi 12).const_mul a) (integrable_const b), integral_const_mul,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  refine h.trans ((add_le_add (mul_le_mul_of_nonneg_left h12 ha) (le_refl b)).trans
    (le_of_eq ?_))
  dsimp [a, b]
  rw [show T ^ 12 = T ^ (12 - q) * T ^ q by
    rw [← pow_add, Nat.sub_add_cancel hq12]]
  field_simp <;> ring

variable {n : ℕ} {Φ : (Fin n → ℝ) → ℝ} {L C : ℝ}

theorem psi_lower12 (hn : 2 ≤ n) (D : Design n) (c : Ret n)
    (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ t x, 0 < t → Φ (t • x) = t * Φ x) (hC : 0 < C)
    (h12 : ∫ a, ∫ v, psiA Φ D c a v ^ 12 ∂stdGauss (Fin (n - 1))
      ∂muI n ≤ (C / n) ^ 12) {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, psiA Φ D c a v ^ q ∂stdGauss (Fin (n - 1))
      ∂muI n ≤ (C / n) ^ q := by
  let μ := (muI n).prod (stdGauss (Fin (n - 1)))
  let g : Ix n × (Fin (n - 1) → ℝ) → ℝ := fun p => psiA Φ D c p.1 p.2
  have hb := psiA_bounds hn D c hL0 hL hhom
  have hm : Measurable g := measurable_psiA (hL.continuous hL0) D c
  have hi (k : ℕ) : Integrable (fun p => g p ^ k) μ := by
    apply Integrable.of_bound (hm.pow_const k).aestronglyMeasurable ((2 * L ^ 2) ^ k)
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hb p.1 p.2).1 _)]
      exact pow_le_pow_left₀ (hb p.1 p.2).1 (hb p.1 p.2).2 k
  have he (k : ℕ) : (∫ p, g p ^ k ∂μ) =
      ∫ a, ∫ v, psiA Φ D c a v ^ k ∂stdGauss (Fin (n - 1)) ∂muI n :=
    integral_prod _ (hi k)
  rw [← he 12] at h12
  rw [← he q]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact moment_lower12 hm (fun p => (hb p.1 p.2).1) hi (div_pos hC hn0) h12 hq hq12

/-- The paper variance denominator follows from the stronger existing denominator. -/
theorem latitude_variance (hn : 4 ≤ n) (D : Design n) (c : Ret n)
    (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ t x, 0 < t → Φ (t • x) = t * Φ x) (hC : 0 < C)
    (h12 : ∫ a, ∫ v, psiA Φ D c a v ^ 12 ∂stdGauss (Fin (n - 1))
      ∂muI n ≤ (C / n) ^ 12) :
    ∫ a, (∫ v, (Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤
      (C / ((n : ℝ) * ((n : ℝ) - 3))) ^ 2 := by
  have h2 := psi_lower12 (by omega) D c hL0 hL hhom hC h12 (q := 2)
    (by norm_num) (by norm_num)
  refine (int_var_psi (by omega) D c hL0 hL hhom hC.le h2).trans ?_
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : C / n / ((n : ℝ) - 2) ≤ C / n / ((n : ℝ) - 3) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  rw [← div_div]
  exact pow_le_pow_left₀ (div_nonneg (div_nonneg hC.le (by linarith))
    (by linarith)) hden 2

/-- The order-two branch retains the sharp constant one. -/
theorem latitude_second (hn : 4 ≤ n) (D : Design n) (c : Ret n)
    (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ t x, 0 < t → Φ (t • x) = t * Φ x) (hC : 0 < C)
    (h12 : ∫ a, ∫ v, psiA Φ D c a v ^ 12 ∂stdGauss (Fin (n - 1))
      ∂muI n ≤ (C / n) ^ 12) :
    ∫ a, ∫ v, |Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))| ^ 2
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      C / ((n : ℝ) * ((n : ℝ) - 3)) := by
  let ν := stdGauss (Fin (n - 1))
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hb := psiA_bounds (by omega) D c hL0 hL hhom
  have hm := measurable_psiA (hL.continuous hL0) D c
  have him : Integrable (fun a => ∫ v, psiA Φ D c a v ∂ν) (muI n) := by
    apply Integrable.of_bound
      (hm.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
      (2 * L ^ 2)
    apply ae_of_all
    intro a
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun v => (hb a v).1)]
    calc
      (∫ v, psiA Φ D c a v ∂ν) ≤ ∫ _v, 2 * L ^ 2 ∂ν := by
        exact integral_mono_of_nonneg (ae_of_all _ fun v => (hb a v).1)
          (integrable_const _) (ae_of_all _ fun v => (hb a v).2)
      _ = 2 * L ^ 2 := by simp
  have h := integral_mono_of_nonneg
    (ae_of_all (muI n) fun a => integral_nonneg fun v => sq_nonneg _)
    (him.div_const ((n : ℝ) - 2))
    (ae_of_all _ fun a => idx_var_psi (by omega) D c hL0 hL hhom a)
  have h1 := psi_lower12 (by omega) D c hL0 hL hhom hC h12 (q := 1)
    (by norm_num) (by norm_num)
  simp only [pow_one] at h1
  simp only [sq_abs]
  refine h.trans ?_
  rw [integral_div]
  calc (∫ a, ∫ v, psiA Φ D c a v ∂ν ∂muI n) / ((n : ℝ) - 2)
      ≤ (C / n) / ((n : ℝ) - 2) :=
        div_le_div_of_nonneg_right h1 (by linarith)
    _ ≤ (C / n) / ((n : ℝ) - 3) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
    _ = _ := by rw [div_div]

/-- The realized certificate supplies every even latitude order from four to twenty-four. -/
theorem latitude_moment (hn : 26 ≤ n) (D : Design n) (c : Ret n)
    (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ t x, 0 < t → Φ (t • x) = t * Φ x) (hC : 0 < C)
    (h12 : ∫ a, ∫ v, psiA Φ D c a v ^ 12 ∂stdGauss (Fin (n - 1))
      ∂muI n ≤ (C / n) ^ 12) {q : ℕ} (hq : 2 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))| ^ (2 * q)
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (BstLean.Part195.rotationConstant q *
        √(C / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q)))) ^ (2 * q) := by
  have hq1 : 1 ≤ q := by omega
  have hqn : 2 * q < n - 1 := by omega
  have hb := int_mom_psi_s (by omega) D c hL0 hL hhom hq1 hqn hC.le
    (psi_lower12 (by omega) D c hL0 hL hhom hC h12 hq1 hq12)
  have hrot : BstLean.Part195.rotationConstant q = cLS q := by
    simp [BstLean.Part195.rotationConstant, show q ≠ 1 by omega,
      BstLean.Part195.oddMoment_eq, cLS]
  rw [hrot]
  convert hb using 2
  unfold kLSs
  have hnR : (26 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq12
  have hden : 0 ≤ (n : ℝ) - 1 - 2 * q := by linarith
  rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    mul_assoc, ← Real.sqrt_mul (inv_nonneg.mpr hden)]
  congr 2
  field_simp

theorem latitude_moment_all (hn : 26 ≤ n) (D : Design n) (c : Ret n)
    (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ t x, 0 < t → Φ (t • x) = t * Φ x) (hC : 0 < C)
    (h12 : ∫ a, ∫ v, psiA Φ D c a v ^ 12 ∂stdGauss (Fin (n - 1))
      ∂muI n ≤ (C / n) ^ 12) {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))| ^ (2 * q)
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (BstLean.Part195.rotationConstant q *
        √(C / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q)))) ^ (2 * q) := by
  by_cases hq1 : q = 1
  · subst q
    have hnR : (26 : ℝ) ≤ n := by exact_mod_cast hn
    have hnonneg : 0 ≤ C / ((n : ℝ) * ((n : ℝ) - 3)) :=
      div_nonneg hC.le (mul_nonneg (by linarith) (by linarith))
    simpa only [BstLean.Part195.rotationConstant_one, Nat.cast_one, mul_one,
      one_mul, show (n : ℝ) - 1 - 2 = (n : ℝ) - 3 by ring,
      Real.sq_sqrt hnonneg] using
      latitude_second (by omega) D c hL0 hL hhom hC h12
  · exact latitude_moment hn D c hL0 hL hhom hC h12 (by omega) hq12

theorem latitude_variance_norm (hn : 4 ≤ n) (D : Design n) (c : Ret n)
    (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ t x, 0 < t → Φ (t • x) = t * Φ x) (hC : 0 < C)
    (h12 : ∫ a, ∫ v, psiA Φ D c a v ^ 12 ∂stdGauss (Fin (n - 1))
      ∂muI n ≤ (C / n) ^ 12) :
    √(∫ a, (∫ v, (Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n) ≤
      C / ((n : ℝ) * ((n : ℝ) - 3)) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 ≤ C / ((n : ℝ) * ((n : ℝ) - 3)) :=
    div_nonneg hC.le (mul_nonneg (by linarith) (by linarith))
  exact Real.sqrt_le_iff.mpr ⟨h0, latitude_variance hn D c hL0 hL hhom hC h12⟩
end BstLean.Part212
