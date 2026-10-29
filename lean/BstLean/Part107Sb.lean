import BstLean.Part107Sa

/-!
# Part 107 S(b): the conditional moments of the realized spread for one fixed `W`
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory

variable {U Θ : Type*} [MeasurableSpace U] [MeasurableSpace Θ]
  {γ : Measure Θ} [IsProbabilityMeasure γ] {f : Θ → U → ℝ} {Q : Θ → ℝ} {κ : U → U → ℝ}
  {a b C : ℝ} {ν : Measure U} [IsProbabilityMeasure ν]

/-- Step 2 and step 3 of Lemma S for one fixed `W`:
`E X = a(K − v)`, `E X² ≤ b((K − v)² + 2D)`, `(v − c)² ≤ D`. -/
theorem Setup.fixedW (H : Setup γ f Q κ a b C) (hb : 0 ≤ b) {K : ℝ}
    (hK : ∀ᵐ u ∂ν, κ u u = K) (c : ℝ) :
    ∫ θ, (∫ u, f θ u ^ 2 ∂ν - (∫ u, f θ u ∂ν) ^ 2) ∂γ =
        a * (K - ∫ p, κ p.1 p.2 ∂(ν.prod ν)) ∧
      ∫ θ, (∫ u, f θ u ^ 2 ∂ν - (∫ u, f θ u ∂ν) ^ 2) ^ 2 ∂γ ≤
        b * ((K - ∫ p, κ p.1 p.2 ∂(ν.prod ν)) ^ 2 +
          2 * ∫ p, (κ p.1 p.2 - c) ^ 2 ∂(ν.prod ν)) ∧
      ((∫ p, κ p.1 p.2 ∂(ν.prod ν)) - c) ^ 2 ≤ ∫ p, (κ p.1 p.2 - c) ^ 2 ∂(ν.prod ν) := by
  have hX : ∀ θ, ∫ u, f θ u ^ 2 ∂ν - (∫ u, f θ u ∂ν) ^ 2 =
      Mp f ν id id θ - Mp f (ν.prod ν) Prod.fst Prod.snd θ := by
    intro θ
    unfold Mp
    rw [integral_prod_mul (fun u => f θ u) (fun u => f θ u)]
    simp only [id, sq]
  simp_rw [hX]
  set M2 := Mp f ν id id with hM2
  set M1 := Mp f (ν.prod ν) Prod.fst Prod.snd with hM1
  set v := ∫ p, κ p.1 p.2 ∂(ν.prod ν) with hv
  have mi : Measurable (id : U → U) := measurable_id
  have m1 : Measurable (Prod.fst : U × U → U) := measurable_fst
  have m2 : Measurable (Prod.snd : U × U → U) := measurable_snd
  -- integrability of the kernel
  have iκ : Integrable (fun p : U × U => κ p.1 p.2) (ν.prod ν) :=
    bm_int H.hκ C fun p => H.hκC _ _
  have hsqb : ∀ x : ℝ, |x| ≤ C → |x ^ 2| ≤ C ^ 2 := fun x hx => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have iκ2 : Integrable (fun p : U × U => κ p.1 p.2 ^ 2) (ν.prod ν) :=
    bm_int (H.hκ.pow_const 2) (C ^ 2) fun p => hsqb _ (H.hκC _ _)
  set kb : U → ℝ := fun u => ∫ u', κ u u' ∂ν with hkb
  have kbm : Measurable kb := H.hκ.stronglyMeasurable.integral_prod_right'.measurable
  have kbC : ∀ u, |kb u| ≤ C := fun u => abs_int_le C fun u' => H.hκC _ _
  have ikb : Integrable kb ν := bm_int kbm C kbC
  have ikb2 : Integrable (fun u => kb u ^ 2) ν :=
    bm_int (kbm.pow_const 2) (C ^ 2) fun u => hsqb _ (kbC u)
  have hvkb : ∫ u, kb u ∂ν = v := (integral_prod _ iκ).symm
  set I2 := ∫ p, κ p.1 p.2 ^ 2 ∂(ν.prod ν) with hI2
  set Kb := ∫ u, kb u ^ 2 ∂ν with hKb
  have hKK : ∫ u, κ u u ∂ν = K := by
    rw [integral_congr_ae hK, integral_const]; simp
  -- first moments
  have E2 : ∫ θ, M2 θ ∂γ = a * K := by
    rw [hM2, H.Mp_two mi mi]; simp only [id]; rw [hKK]
  have E1 : ∫ θ, M1 θ ∂γ = a * v := H.Mp_two m1 m2
  -- second moments
  have hI2' : ∫ u, ∫ u', κ u u' * κ u u' ∂ν ∂ν = I2 := by
    rw [hI2, integral_prod _ iκ2]; simp only [sq]
  have F22 : ∫ θ, M2 θ * M2 θ ∂γ = b * (K * K + I2 + I2) := by
    rw [hM2, H.Mp_four mi mi mi mi]; simp only [id]; rw [hKK, hI2']
  have inner1 : ∀ x y : U, ∫ p' : U × U, κ x p'.1 * κ y p'.2 ∂(ν.prod ν) = kb x * kb y :=
    fun x y => integral_prod_mul (fun z => κ x z) (fun z => κ y z)
  have inner2 : ∀ x y : U, ∫ p' : U × U, κ x p'.2 * κ y p'.1 ∂(ν.prod ν) = kb x * kb y := by
    intro x y
    rw [mul_comm (kb x) (kb y), ← inner1 y x]
    exact integral_congr_ae (ae_of_all _ fun p => mul_comm _ _)
  have hKb' : ∫ u, kb u * kb u ∂ν = Kb := by simp only [hKb, sq]
  have F21 : ∫ θ, M2 θ * M1 θ ∂γ = b * (K * v + Kb + Kb) := by
    rw [hM2, hM1, H.Mp_four mi mi m1 m2]; simp only [id]
    simp_rw [inner1, inner2]; rw [hKK, hKb']
  have hvv : ∫ p : U × U, kb p.1 * kb p.2 ∂(ν.prod ν) = v * v := by
    rw [integral_prod_mul kb kb, hvkb]
  have F11 : ∫ θ, M1 θ * M1 θ ∂γ = b * (v * v + v * v + v * v) := by
    rw [hM1, H.Mp_four m1 m2 m1 m2]
    simp_rw [inner1, inner2]; rw [hvv]
  have i22 := H.MM_int mi mi mi mi (ρ := ν) (ρ' := ν)
  have i21 := H.MM_int mi mi m1 m2 (ρ := ν) (ρ' := ν.prod ν)
  have i11 := H.MM_int m1 m2 m1 m2 (ρ := ν.prod ν) (ρ' := ν.prod ν)
  have EX2 : ∫ θ, (M2 θ - M1 θ) ^ 2 ∂γ =
      b * (K * K + I2 + I2) - 2 * (b * (K * v + Kb + Kb)) + b * (v * v + v * v + v * v) := by
    have e : (fun θ => (M2 θ - M1 θ) ^ 2) =
        fun θ => M2 θ * M2 θ - 2 * (M2 θ * M1 θ) + M1 θ * M1 θ := by funext θ; ring
    have ic : Integrable (fun θ => 2 * (M2 θ * M1 θ)) γ := i21.const_mul 2
    have is : Integrable (fun θ => M2 θ * M2 θ - 2 * (M2 θ * M1 θ)) γ := i22.sub ic
    rw [e, integral_add is i11, integral_sub i22 ic, integral_const_mul, F22, F21, F11]
  -- the kernel inequalities
  have hD : ∫ p, (κ p.1 p.2 - c) ^ 2 ∂(ν.prod ν) = I2 - 2 * c * v + c ^ 2 := by
    have e : (fun p : U × U => (κ p.1 p.2 - c) ^ 2) =
        fun p => κ p.1 p.2 ^ 2 - 2 * c * κ p.1 p.2 + c ^ 2 := by funext p; ring
    have ic : Integrable (fun p : U × U => 2 * c * κ p.1 p.2) (ν.prod ν) := iκ.const_mul _
    have is : Integrable (fun p : U × U => κ p.1 p.2 ^ 2 - 2 * c * κ p.1 p.2) (ν.prod ν) :=
      iκ2.sub ic
    rw [e, integral_add is (integrable_const _), integral_sub iκ2 ic, integral_const_mul,
      integral_const]
    simp [hI2, hv]
  have hJ1 : v ^ 2 ≤ Kb := by
    have := sq_int_le ikb ikb2
    rwa [hvkb] at this
  have hJ2 : (v - c) ^ 2 ≤ I2 - 2 * c * v + c ^ 2 := by
    have := sq_int_le (g := fun p : U × U => κ p.1 p.2 - c) (iκ.sub (integrable_const c)) (by
      have e : (fun p : U × U => (κ p.1 p.2 - c) ^ 2) =
        fun p => κ p.1 p.2 ^ 2 - 2 * c * κ p.1 p.2 + c ^ 2 := by funext p; ring
      show Integrable (fun p : U × U => (κ p.1 p.2 - c) ^ 2) (ν.prod ν)
      rw [e]
      exact (iκ2.sub (iκ.const_mul _)).add (integrable_const _))
    have e2 : ∫ p : U × U, (κ p.1 p.2 - c) ∂(ν.prod ν) = v - c := by
      rw [integral_sub iκ (integrable_const c), integral_const]; simp [hv]
    rw [e2, hD] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_sub (H.Mp_int mi mi) (H.Mp_int m1 m2), E2, E1]; ring
  · rw [EX2, hD]
    have : b * (K * K + I2 + I2) - 2 * (b * (K * v + Kb + Kb)) + b * (v * v + v * v + v * v) =
        b * ((K - v) ^ 2 + 2 * (I2 - 2 * c * v + c ^ 2)) -
          b * (4 * (Kb - v ^ 2) + 2 * (v - c) ^ 2) := by ring
    rw [this]
    have : 0 ≤ b * (4 * (Kb - v ^ 2) + 2 * (v - c) ^ 2) :=
      mul_nonneg hb (by nlinarith [sq_nonneg (v - c)])
    linarith
  · rw [hD]; exact hJ2

end BstLean.Part107
