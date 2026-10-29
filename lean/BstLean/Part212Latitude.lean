import BstLean.Part212Inverse
import BstLean.Part212Radius
import BstLean.Part166Th

/-! The latitude coefficient uses the sharp noncentral inverse moment. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real Filter Topology Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157
open BstLean.Part150 (thetaC rhoC)
open BstLean.Part161 (Ix muI consV consV_map measurable_consV normSq_consV)

noncomputable def inverseLatitudeCoefficient (n j : ℕ) (θ : ℝ) : ℝ :=
  θ / (1 - (2 * j + 2 : ℝ) * θ / n)

noncomputable def latitudeCoefficient (n p : ℕ) (θ : ℝ) : ℝ :=
  inverseLatitudeCoefficient n (2 * p) θ * ((n : ℝ) + 4 * p - 3) / n

theorem inverseLatitude_identity {n j : ℕ} (hn : 2 * j + 2 < n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    inverseLatitudeCoefficient n j (thetaC c τ) / n =
      τ ^ 2 / (normSq c + ((n : ℝ) - 2 * j - 2) * τ ^ 2) := by
  have hnR : (2 * (j : ℝ) + 2) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hR : 0 < normSq c + (n : ℝ) * τ ^ 2 := by
    have := normSq_nonneg c
    positivity
  have hD : 0 < normSq c + ((n : ℝ) - 2 * j - 2) * τ ^ 2 := by
    have := normSq_nonneg c
    exact add_pos_of_nonneg_of_pos this (mul_pos (by linarith) (sq_pos_of_pos hτ))
  unfold inverseLatitudeCoefficient thetaC rhoC
  rw [Real.sq_sqrt hR.le]
  field_simp
  ring

theorem inverseLatitude_moment {n j : ℕ} (hj : 1 ≤ j) (hn : 2 * j + 2 < n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ ξ, ENNReal.ofReal ((τ ^ 2 / normSq (c + τ • ξ)) ^ j) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal ((inverseLatitudeCoefficient n j (thetaC c τ) / n) ^ j) := by
  rw [inverseLatitude_identity hn c hτ]
  exact noncentral_inverse_radius hj hn c hτ

theorem radialProduct_upper (d j : ℕ) (hj : 1 ≤ j) :
    radialProduct d j ≤ ((d : ℝ) + 2 * (j : ℝ) - 2) ^ j := by
  unfold radialProduct
  calc (∏ i ∈ Finset.range j, ((d : ℝ) + 2 * i))
      ≤ ∏ _i ∈ Finset.range j, ((d : ℝ) + 2 * (j : ℝ) - 2) := by
        apply Finset.prod_le_prod₀
        · intro i _; positivity
        · intro i hi
          have hh : i + 1 ≤ j := by have := Finset.mem_range.mp hi; omega
          have hhR : (i : ℝ) + 1 ≤ j := by exact_mod_cast hh
          linarith
    _ = _ := by simp

theorem latitude_ratio {n : ℕ} (hn : 1 ≤ n) (a0 τ : ℝ) (hτ : 0 < τ)
    (a : Ix n) (ha : normSq a.2 ≠ 0) :
    1 - latitude (n := n) a0 τ a ^ 2 =
      τ ^ 2 / normSq (consV (n := n) a0 0 + τ • consV a.1 a.2) * normSq a.2 := by
  have hg : 0 < normSq a.2 := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm ha)
  have hd : 0 < (a0 + τ * a.1) ^ 2 + τ ^ 2 * normSq a.2 := by positivity
  have hnorm : normSq (consV (n := n) a0 0 + τ • consV a.1 a.2) =
      (a0 + τ * a.1) ^ 2 + τ ^ 2 * normSq a.2 := by
    rw [← BstLean.Part161.consV_smul, ← BstLean.Part161.consV_add,
      normSq_consV hn, zero_add, normSq_smul]
  unfold latitude
  rw [div_pow, Real.sq_sqrt hd.le, hnorm]
  field_simp
  ring

theorem young_product {lam f g : ℝ} (hLam : 0 < lam) :
    f * g ≤ lam / 2 * f ^ 2 + (2 * lam)⁻¹ * g ^ 2 := by
  have h : 0 ≤ (lam * f - g) ^ 2 / (2 * lam) := div_nonneg (sq_nonneg _) (by positivity)
  have he : (lam * f - g) ^ 2 / (2 * lam) =
      lam / 2 * f ^ 2 + (2 * lam)⁻¹ * g ^ 2 - f * g := by field_simp; ring
  rw [he] at h
  linarith
theorem latitude_moment_exact {n p : ℕ} (hp : 1 ≤ p) (hn : 4 * p + 2 < n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ p)
      ∂muI n ≤ ENNReal.ofReal (latitudeCoefficient n p (thetaC c τ) ^ p) := by
  letI : IsProbabilityMeasure (stdGauss (Fin (n - 1))) := by unfold stdGauss; infer_instance
  letI : SFinite (stdGauss (Fin (n - 1))) := inferInstance
  have hn1 : 1 ≤ n := by omega
  let c' : Fin n → ℝ := consV (√(normSq c)) 0
  have hcc : normSq c' = normSq c := by
    dsimp [c']
    rw [normSq_consV hn1, Real.sq_sqrt (normSq_nonneg c)]
    simp [normSq]
  let A := τ ^ 2 / (normSq c + ((n : ℝ) - 4 * p - 2) * τ ^ 2)
  let D := (n : ℝ) + 4 * p - 3
  have hnR : 4 * (p : ℝ) + 2 < n := by exact_mod_cast hn
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos (sq_pos_of_pos hτ) (add_pos_of_nonneg_of_pos (normSq_nonneg c)
      (mul_pos (by linarith) (sq_pos_of_pos hτ)))
  have hD : 0 < D := by dsimp [D]; linarith
  let f := fun a : Ix n => ENNReal.ofReal
    ((τ ^ 2 / normSq (c' + τ • consV a.1 a.2)) ^ p)
  let g := fun a : Ix n => ENNReal.ofReal (normSq a.2 ^ p)
  have hf : Measurable f :=
    ((measurable_const.div (measurable_normSq.comp
      (measurable_const.add (measurable_consV.const_smul τ)))).pow_const p).ennreal_ofReal
  have hg : Measurable g :=
    ((measurable_normSq.comp measurable_snd).pow_const p).ennreal_ofReal
  have hfi : ∫⁻ a, f a ^ (2 : ℝ) ∂muI n ≤ ENNReal.ofReal (A ^ (2 * p)) := by
    simp only [f, ENNReal.rpow_two, ← ENNReal.ofReal_pow
      (pow_nonneg (div_nonneg (sq_nonneg τ) (normSq_nonneg _)) p), ← pow_mul]
    rw [show p * 2 = 2 * p by omega]
    have hm : Measurable (fun ξ : Fin n → ℝ =>
        ENNReal.ofReal ((τ ^ 2 / normSq (c' + τ • ξ)) ^ (2 * p))) :=
      ((measurable_const.div (measurable_normSq.comp
        (measurable_const.add (measurable_id.const_smul τ)))).pow_const (2 * p)).ennreal_ofReal
    rw [← lintegral_map hm measurable_consV, muI, consV_map hn1]
    have h := noncentral_inverse_radius (n := n) (j := 2 * p) (by omega) (by omega) c' hτ
    have he : (n : ℝ) - 2 * (2 * p : ℕ) - 2 = (n : ℝ) - 4 * p - 2 := by
      push_cast
      ring
    simpa only [hcc, he, A] using h
  have hgi : ∫⁻ a, g a ^ (2 : ℝ) ∂muI n ≤ ENNReal.ofReal (D ^ (2 * p)) := by
    simp only [g, ENNReal.rpow_two, ← ENNReal.ofReal_pow
      (pow_nonneg (normSq_nonneg _) p), ← pow_mul]
    rw [show p * 2 = 2 * p by omega]
    have hm : Measurable (fun a : Ix n => ENNReal.ofReal (normSq a.2 ^ (2 * p))) :=
      ((measurable_normSq.comp measurable_snd).pow_const (2 * p)).ennreal_ofReal
    rw [muI, lintegral_prod _ hm.aemeasurable]
    simp only [lintegral_const, measure_univ, smul_eq_mul, mul_one]
    have heRad (v : Fin (n - 1) → ℝ) : normSq v ^ (2 * p) =
        BstLean.Part53.radF53 v ^ (2 * (2 * p)) := by
      unfold BstLean.Part53.radF53
      change normSq v ^ (2 * p) = (√(normSq v)) ^ (2 * (2 * p))
      rw [pow_mul (√(normSq v)) 2 (2 * p), Real.sq_sqrt (normSq_nonneg v)]
    simp_rw [heRad]
    rw [radius_even_lintegral (n - 1) (2 * p) (by omega)]
    apply ENNReal.ofReal_le_ofReal
    have h := radialProduct_upper (n - 1) (2 * p) (by omega)
    have he : ((n - 1 : ℕ) : ℝ) + 2 * (2 * p : ℕ) - 2 = D := by
      dsimp [D]
      rw [Nat.cast_sub hn1]
      push_cast
      ring
    simpa only [he] using h
  have hae : ∀ᵐ a ∂muI n, normSq a.2 ≠ 0 := by
    have hz : muI n {a : Ix n | normSq a.2 = 0} = 0 := by
      have he : {a : Ix n | normSq a.2 = 0} =
          Set.univ ×ˢ {v : Fin (n - 1) → ℝ | normSq v = 0} := by ext a; simp
      rw [he, muI, Measure.prod_prod, BstLean.Part161.stdGauss_normSq_zero (by omega),
        mul_zero]
    exact measure_eq_zero_iff_ae_notMem.mp hz
  have hleft : (∫⁻ a, ENNReal.ofReal
      ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ p) ∂muI n) =
      ∫⁻ a, (f * g) a ∂muI n := by
    apply lintegral_congr_ae
    filter_upwards [hae] with a ha
    rw [latitude_ratio hn1 _ _ hτ a ha, mul_pow]
    exact ENNReal.ofReal_mul (pow_nonneg
      (div_nonneg (sq_nonneg τ) (normSq_nonneg _)) p)
  rw [hleft]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (muI n)
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
    hf.aemeasurable hg.aemeasurable
  refine hh.trans ?_
  have hroot (x : ℝ) (hx : 0 ≤ x) :
      ENNReal.ofReal (x ^ (2 * p)) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (x ^ p) := by
    rw [show 2 * p = p * 2 by omega, pow_mul, ENNReal.ofReal_pow (pow_nonneg hx p),
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ a, f a ^ (2 : ℝ) ∂muI n) ^ ((1 : ℝ) / 2) *
        (∫⁻ a, g a ^ (2 : ℝ) ∂muI n) ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (A ^ (2 * p)) ^ ((1 : ℝ) / 2) *
        ENNReal.ofReal (D ^ (2 * p)) ^ ((1 : ℝ) / 2) := by gcongr
    _ = ENNReal.ofReal ((A * D) ^ p) := by
      rw [hroot A hA.le, hroot D hD.le, ← ENNReal.ofReal_mul (pow_nonneg hA.le p),
        ← mul_pow]
    _ = _ := by
      congr 2
      have hi := inverseLatitude_identity (j := 2 * p) (by omega) c hτ
      unfold latitudeCoefficient
      rw [show inverseLatitudeCoefficient n (2 * p) (thetaC c τ) *
          ((n : ℝ) + 4 * p - 3) / n =
          (inverseLatitudeCoefficient n (2 * p) (thetaC c τ) / n) * D by dsimp [D]; ring,
        hi]
      dsimp [A]
      push_cast
      ring
theorem inverseLatitudeCoefficient_mono {n j : ℕ} (hn : 2 * j + 2 < n)
    {θ θ' : ℝ} (hθ : 0 ≤ θ) (hθθ' : θ ≤ θ') (hθ' : θ' ≤ 1) :
    inverseLatitudeCoefficient n j θ ≤ inverseLatitudeCoefficient n j θ' := by
  have hnR : 2 * (j : ℝ) + 2 < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ha : 0 ≤ 2 * (j : ℝ) + 2 := by positivity
  have hd' : 0 < (n : ℝ) - (2 * j + 2) * θ' := by
    have h := mul_le_mul_of_nonneg_left hθ' ha
    linarith
  have hd : 0 < (n : ℝ) - (2 * j + 2) * θ := by
    have h := mul_le_mul_of_nonneg_left hθθ' ha
    linarith
  have he (x : ℝ) : inverseLatitudeCoefficient n j x =
      (n : ℝ) * x / (n - (2 * j + 2) * x) := by
    unfold inverseLatitudeCoefficient
    field_simp
  rw [he θ, he θ', div_le_div_iff₀ hd hd']
  nlinarith [mul_le_mul_of_nonneg_left hθθ' (sq_nonneg (n : ℝ))]

theorem latitudeCoefficient_mono {n p : ℕ} (hp : 1 ≤ p) (hn : 4 * p + 2 < n)
    {θ θ' : ℝ} (hθ : 0 ≤ θ) (hθθ' : θ ≤ θ') (hθ' : θ' ≤ 1) :
    latitudeCoefficient n p θ ≤ latitudeCoefficient n p θ' := by
  have hnR : 4 * (p : ℝ) + 2 < n := by exact_mod_cast hn
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h := inverseLatitudeCoefficient_mono (n := n) (j := 2 * p) (by omega) hθ hθθ' hθ'
  unfold latitudeCoefficient
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact mul_le_mul_of_nonneg_right h (by linarith)
end BstLean.Part212
