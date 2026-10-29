import BstLean.Part181Jen
import BstLean.Part153PPs2

/-! Part 199: moment reductions with variable orders and dimension guards. -/
namespace BstLean.Part199
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part160
open BstLean.Part153 (jacT Xi4 nuA jS)

lemma power_fraction_le {p q : ℕ} (hp : 0 < p) (hq : q ≤ p) {y : ℝ} (hy : 0 ≤ y) :
    y ^ q ≤ (q : ℝ) / p * y ^ p + (1 - (q : ℝ) / p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (q : ℝ) ≤ p := by exact_mod_cast hq
  have hα : 0 ≤ (q : ℝ) / p := by positivity
  have hα1 : (q : ℝ) / p ≤ 1 := (div_le_one hpR).mpr hqR
  have h := Real.geom_mean_le_arith_mean2_weighted hα (by linarith : 0 ≤ 1 - (q : ℝ) / p)
    (pow_nonneg hy p) zero_le_one (by ring)
  rw [Real.one_rpow, mul_one, mul_one] at h
  have he : (y ^ p) ^ ((q : ℝ) / p) = y ^ q := by
    rw [← Real.rpow_natCast y p, ← Real.rpow_mul hy, ← Real.rpow_natCast y q]
    congr 1
    field_simp
  rwa [he] at h

/-- A proved order-p moment bound supplies each lower integer moment. -/
theorem integral_power_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    {p q : ℕ} (hp : 0 < p) (hq : q ≤ p)
    (hip : Integrable (fun x => f x ^ p) μ) (hiq : Integrable (fun x => f x ^ q) μ)
    {B : ℝ} (hB : 0 < B) (hbound : ∫ x, f x ^ p ∂μ ≤ B ^ p) :
    ∫ x, f x ^ q ∂μ ≤ B ^ q := by
  have hpt : ∀ x, f x ^ q ≤ B ^ q *
      ((q : ℝ) / p * (f x ^ p / B ^ p) + (1 - (q : ℝ) / p)) := by
    intro x
    have h := power_fraction_le hp hq (div_nonneg (hf0 x) hB.le)
    rw [div_pow, div_pow] at h
    have he : f x ^ q = B ^ q * (f x ^ q / B ^ q) := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left h (pow_nonneg hB.le q)
  have hi := (((hip.div_const (B ^ p)).const_mul ((q : ℝ) / p)).add
    (integrable_const (1 - (q : ℝ) / p))).const_mul (B ^ q)
  refine (integral_mono hiq hi hpt).trans ?_
  simp only [Pi.add_apply]
  rw [integral_const_mul, integral_add ((hip.div_const (B ^ p)).const_mul ((q : ℝ) / p))
      (integrable_const (1 - (q : ℝ) / p)),
    integral_const_mul, integral_div, integral_const]
  simp only [probReal_univ, one_smul]
  have hb : (∫ x, f x ^ p ∂μ) / B ^ p ≤ 1 := (div_le_one (pow_pos hB p)).mpr hbound
  have hα : 0 ≤ (q : ℝ) / p := by positivity
  have hαb := mul_le_mul_of_nonneg_left hb hα
  have hinside : (q : ℝ) / p * ((∫ x, f x ^ p ∂μ) / B ^ p) +
      (1 - (q : ℝ) / p) ≤ 1 := by linarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hinside (pow_nonneg hB.le q)

theorem Wq_le_of_Wp {n p q : ℕ} (hp : 0 < p) (hq : q ≤ p) (hn : 2 * p + 1 < n)
    (c : Fin n → ℝ) {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B)
    (h : WqN p c τ ≤ B ^ p) : WqN q c τ ≤ B ^ q := by
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  exact integral_power_le (stdGauss (Fin n)) (wq_nonneg c τ) hp hq
    (integrable_wqq hn c hτ) (integrable_wqq (by omega) c hτ) hB h

theorem Xq_le_of_Xp {n p q : ℕ} (hp : 0 < p) (hq : q ≤ p) (hn : 2 * p + 1 < n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ)
    {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B) (h : XqN p A₁ A₂ c τ ≤ B ^ p) :
    XqN q A₁ A₂ c τ ≤ B ^ q := by
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  let f := fun ξ : Fin n → ℝ =>
    τ ^ 2 * (normSq (c + τ • ξ))⁻¹ * opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2
  have he : ∀ k, XqN k A₁ A₂ c τ = ∫ ξ, f ξ ^ k ∂stdGauss (Fin n) := by
    intro k
    unfold XqN
    simp only [f, mul_pow]
  have hi : ∀ k, 2 * k + 1 < n → Integrable (fun ξ => f ξ ^ k) (stdGauss (Fin n)) := by
    intro k hk
    simpa only [f, mul_pow] using BstLean.Part181.integrable_xq hk A₁ A₂ c hτ
  rw [he] at h ⊢
  exact integral_power_le (stdGauss (Fin n)) (fun ξ =>
    mul_nonneg (wq_nonneg c τ ξ) (sq_nonneg _))
    hp hq (hi p hn) (hi q (by omega)) hB h

/-- Variable-order input moments supply the exceptional-pair coefficient. -/
theorem Xi4_le_of_Xp {n p : ℕ} (hp : 2 ≤ p) (hn : 2 * p + 1 < n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ)
    {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B) (h : XqN p A₁ A₂ c τ ≤ B ^ p) :
    Xi4 A₁ A₂ c τ ≤ B * (2 / (n : ℝ)) / n := by
  have h2 := Xq_le_of_Xp (by omega) hp hn A₁ A₂ c hτ hB h
  have hs : √(XqN 2 A₁ A₂ c τ) ≤ B := by
    exact (Real.sqrt_le_sqrt h2).trans (le_of_eq (Real.sqrt_sq hB.le))
  rw [Xi4_eq_XqN]
  refine (mul_le_mul_of_nonneg_left hs (by positivity)).trans (le_of_eq ?_)
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm]
  ring

/-- The moment event has variable order and multiplier. -/
def MomentEvent (n p : ℕ) (M : ℝ) : Set (AgFam n) :=
  {k | XqN p k.2.1 k.2.2 k.1.1 k.1.2 ≤ (M * n) ^ p * WqN p k.1.1 k.1.2}

theorem measurableSet_MomentEvent (n p : ℕ) (M : ℝ) :
    MeasurableSet (MomentEvent n p M) :=
  measurableSet_le (measurable_XqN_fam p) ((measurable_WqN_fam p).const_mul _)

/-- Actual Gaussian weights supply the moment event without a fixed dimension floor. -/
theorem MomentEvent_charge {n p P : ℕ} (hp : 1 ≤ p) (hP : 1 ≤ P)
    (hn : 2 * p + 1 < n) (c : Fin n → ℝ) {τ M η : ℝ}
    (hτ : 0 < τ) (hM : 0 < M) (hη : 0 ≤ η) :
    (nuA n).real {a | ((c, τ), a) ∉ MomentEvent n p M} ≤
      (jS n (p * P) η ^ 2 / M) ^ (p * P) := by
  change (nuA n).real {a | ¬ XqN p a.1 a.2 c τ ≤ (M * n) ^ p * WqN p c τ} ≤ _
  simp only [not_le]
  exact markov_XqN hP hn c hτ (BstLean.Part153.jS_nonneg n (p * P) η)
    (fun _ hx => BstLean.Part153.lemmaPP_i_sharp (by omega)
      (by nlinarith : 1 ≤ p * P) hη hx) hM

end BstLean.Part199
