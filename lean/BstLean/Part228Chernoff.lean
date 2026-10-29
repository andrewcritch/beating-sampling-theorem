import BstLean.Part228Gaussian
import BstLean.Part161Red

/-! Direct latitude Chernoff bounds with variable endpoints and parameters. -/
namespace BstLean.Part228
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part161 (Ix muI)
open BstLean.Part157 (latitude)

noncomputable def endpointRatio (b : ℝ) : ℝ := b ^ 2 / (1 - b ^ 2)

noncomputable def latitudeQuadratic (n : ℕ) (a τ b : ℝ) (p : Ix n) : ℝ :=
  (a + τ * p.1) ^ 2 - endpointRatio b * τ ^ 2 * normSq p.2

noncomputable def chernoffMajorant (n : ℕ) (a τ b t : ℝ) : ℝ :=
  exp (t * a ^ 2 / (1 - 2 * t * τ ^ 2)) * (√(1 - 2 * t * τ ^ 2))⁻¹ *
    (√(1 + 2 * t * endpointRatio b * τ ^ 2))⁻¹ ^ (n - 1)

theorem latitude_quadratic_transform (n : ℕ) {a τ b t : ℝ}
    (hax : 0 < 1 - 2 * t * τ ^ 2)
    (htr : 0 < 1 + 2 * t * endpointRatio b * τ ^ 2) :
    Integrable (fun p : Ix n => exp (t * latitudeQuadratic n a τ b p)) (muI n) ∧
    (∫ p, exp (t * latitudeQuadratic n a τ b p) ∂muI n) =
      chernoffMajorant n a τ b t := by
  have ht : -(t * endpointRatio b * τ ^ 2) < 1 / 2 := by nlinarith
  have hx := square_transform (a := a) (τ := τ) hax
  have hv := central_transform (n - 1) ht
  have he : (fun p : Ix n => exp (t * latitudeQuadratic n a τ b p)) =
      fun p => exp (t * (a + τ * p.1) ^ 2) *
        exp (-(t * endpointRatio b * τ ^ 2) * normSq p.2) := by
    funext p
    rw [← exp_add]
    congr 1
    unfold latitudeQuadratic
    ring
  rw [he]
  constructor
  · exact hx.1.mul_prod hv.1
  · rw [muI, integral_prod_mul (fun x : ℝ => exp (t * (a + τ * x) ^ 2))
      (fun x : Fin (n - 1) → ℝ => exp (-(t * endpointRatio b * τ ^ 2) * normSq x)),
      hx.2, hv.2]
    unfold chernoffMajorant
    congr 3
    ring

theorem upper_endpoint_inclusion {T q b : ℝ} (hq : 0 ≤ q) (hb : 0 < b)
    (hb1 : b < 1) (hs : b < T / √(T ^ 2 + q)) :
    0 ≤ T ^ 2 - endpointRatio b * q := by
  have hN : 0 < T ^ 2 + q := by
    by_contra h
    have he : T ^ 2 + q = 0 := le_antisymm (not_lt.mp h) (by positivity)
    simp only [he, sqrt_zero, div_zero] at hs
    linarith
  have hden := sqrt_pos.mpr hN
  have hTb : b * √(T ^ 2 + q) < T := (lt_div_iff₀ hden).mp hs
  have hT : 0 ≤ T := (lt_trans (by positivity) hTb).le
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ b * √(T ^ 2 + q)) hTb.le 2
  rw [mul_pow, sq_sqrt hN.le] at hsq
  have hbD : 0 < 1 - b ^ 2 := by nlinarith
  have hineq : b ^ 2 * q ≤ T ^ 2 * (1 - b ^ 2) := by nlinarith
  have hh : endpointRatio b * q ≤ T ^ 2 := by
    unfold endpointRatio
    rw [div_mul_eq_mul_div, div_le_iff₀ hbD]
    exact hineq
  linarith

theorem lower_endpoint_inclusion {T q b : ℝ} (hq : 0 ≤ q) (hb : 0 < b)
    (hb1 : b < 1) (hT : 0 < T) (hs : T / √(T ^ 2 + q) < b) :
    T ^ 2 - endpointRatio b * q ≤ 0 := by
  have hN : 0 < T ^ 2 + q := add_pos_of_pos_of_nonneg (sq_pos_of_pos hT) hq
  have hTb : T < b * √(T ^ 2 + q) := (div_lt_iff₀ (sqrt_pos.mpr hN)).mp hs
  have hsq := pow_le_pow_left₀ hT.le hTb.le 2
  rw [mul_pow, sq_sqrt hN.le] at hsq
  have hbD : 0 < 1 - b ^ 2 := by nlinarith
  have hh : T ^ 2 ≤ endpointRatio b * q := by
    unfold endpointRatio
    rw [div_mul_eq_mul_div, le_div_iff₀ hbD]
    nlinarith
  linarith

theorem latitude_upper_tail (n : ℕ) {a τ b t : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (ht : 0 ≤ t)
    (hax : 0 < 1 - 2 * t * τ ^ 2)
    (htr : 0 < 1 + 2 * t * endpointRatio b * τ ^ 2) :
    (muI n).real {p | b < latitude a τ p} ≤ chernoffMajorant n a τ b t := by
  have h := measure_ge_le_exp_mul_mgf (X := latitudeQuadratic n a τ b) (μ := muI n)
    0 ht (latitude_quadratic_transform n hax htr).1
  simp only [mul_zero, neg_zero, exp_zero, one_mul, mgf] at h
  rw [(latitude_quadratic_transform n hax htr).2] at h
  refine (measureReal_mono ?_).trans h
  intro p hp
  simpa only [latitudeQuadratic, mul_assoc, mem_ofPred_eq] using
    upper_endpoint_inclusion (mul_nonneg (sq_nonneg τ) (normSq_nonneg p.2)) hb hb1 hp

theorem axial_negative_tail {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) :
    (gaussianReal 0 1).real {z | a + τ * z ≤ 0} ≤ exp (-(a ^ 2 / (2 * τ ^ 2))) := by
  have ht : -(a / τ) ≤ 0 := neg_nonpos.mpr (div_nonneg ha hτ.le)
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id)
    (t := -(a / τ)) (-(a / τ)) ht (integrable_exp_mul_gaussianReal _)
  rw [mgf_id_gaussianReal] at h
  simp only [NNReal.coe_one, one_mul, mul_zero, zero_mul, zero_add] at h
  rw [← exp_add] at h
  have he : - -(a / τ) * -(a / τ) + (-(a / τ)) ^ 2 / 2 =
      -(a ^ 2 / (2 * τ ^ 2)) := by field_simp; ring
  rw [he] at h
  refine (measureReal_mono ?_).trans h
  intro z hz
  change a + τ * z ≤ 0 at hz
  change z ≤ -(a / τ)
  rw [← neg_div, le_div_iff₀ hτ]
  nlinarith

theorem latitude_lower_tail (n : ℕ) {a τ b t : ℝ}
    (ha : 0 ≤ a) (hτ : 0 < τ) (hb : 0 < b) (hb1 : b < 1) (ht : t ≤ 0)
    (hax : 0 < 1 - 2 * t * τ ^ 2)
    (htr : 0 < 1 + 2 * t * endpointRatio b * τ ^ 2) :
    (muI n).real {p | latitude a τ p < b} ≤
      exp (-(a ^ 2 / (2 * τ ^ 2))) + chernoffMajorant n a τ b t := by
  have h := measure_le_le_exp_mul_mgf (X := latitudeQuadratic n a τ b) (μ := muI n)
    0 ht (latitude_quadratic_transform n hax htr).1
  simp only [mul_zero, neg_zero, exp_zero, one_mul, mgf] at h
  rw [(latitude_quadratic_transform n hax htr).2] at h
  have hsub : {p : Ix n | latitude a τ p < b} ⊆
      ({z : ℝ | a + τ * z ≤ 0} ×ˢ univ) ∪ {p | latitudeQuadratic n a τ b p ≤ 0} := by
    intro p hp
    by_cases hT : a + τ * p.1 ≤ 0
    · exact Or.inl ⟨hT, mem_univ _⟩
    · right
      simpa only [latitudeQuadratic, mul_assoc, mem_ofPred_eq] using
        lower_endpoint_inclusion (mul_nonneg (sq_nonneg τ) (normSq_nonneg p.2))
          hb hb1 (not_le.mp hT) hp
  have hprod : (muI n).real ({z : ℝ | a + τ * z ≤ 0} ×ˢ univ) =
      (gaussianReal 0 1).real {z | a + τ * z ≤ 0} := by
    simp [muI, measureReal_def, Measure.prod_prod]
  calc (muI n).real _ ≤ (muI n).real
        (({z : ℝ | a + τ * z ≤ 0} ×ˢ univ) ∪ {p | latitudeQuadratic n a τ b p ≤ 0}) :=
      measureReal_mono hsub
    _ ≤ (muI n).real ({z : ℝ | a + τ * z ≤ 0} ×ˢ univ) +
        (muI n).real {p | latitudeQuadratic n a τ b p ≤ 0} := measureReal_union_le _ _
    _ ≤ _ := by rw [hprod]; exact add_le_add (axial_negative_tail ha hτ) h

noncomputable def latitudeTailMass (n : ℕ) (a τ lo hi tl tu : ℝ) : ℝ :=
  exp (-(a ^ 2 / (2 * τ ^ 2))) + chernoffMajorant n a τ lo tl +
    chernoffMajorant n a τ hi tu

noncomputable def latitudeTailRoot (n : ℕ) (a τ lo hi tl tu : ℝ) : ℝ :=
  √(2 * latitudeTailMass n a τ lo hi tl tu)

theorem latitude_interval_tail (n : ℕ) {a τ lo hi tl tu : ℝ}
    (ha : 0 ≤ a) (hτ : 0 < τ) (hlo : 0 < lo) (hlo1 : lo < 1)
    (hhi : 0 < hi) (hhi1 : hi < 1) (htl : tl ≤ 0) (htu : 0 ≤ tu)
    (hlax : 0 < 1 - 2 * tl * τ ^ 2)
    (hltr : 0 < 1 + 2 * tl * endpointRatio lo * τ ^ 2)
    (huax : 0 < 1 - 2 * tu * τ ^ 2)
    (hutr : 0 < 1 + 2 * tu * endpointRatio hi * τ ^ 2) :
    (muI n).real {p | latitude a τ p ∉ Icc lo hi} ≤ latitudeTailMass n a τ lo hi tl tu := by
  have hs : {p : Ix n | latitude a τ p ∉ Icc lo hi} ⊆
      {p | latitude a τ p < lo} ∪ {p | hi < latitude a τ p} := by
    intro p hp
    simp only [mem_ofPred_eq, mem_Icc, not_and_or, not_le, mem_union] at hp ⊢
    exact hp
  exact (measureReal_mono hs).trans ((measureReal_union_le _ _).trans
    (add_le_add (latitude_lower_tail n ha hτ hlo hlo1 htl hlax hltr)
      (latitude_upper_tail n hhi hhi1 htu huax hutr)))

end BstLean.Part228
