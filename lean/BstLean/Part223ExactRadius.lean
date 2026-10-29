import BstLean.Part223RadiusLS

/-! The exact inverse eighth radial moment supplies the paper latitude factor. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Filter Topology Set
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (radF53)
open BstLean.Part53.RemezAux (gaussianRadialFactor gaussianRadialFactor_nonneg
  gaussian_radius_integral)
open BstLean.Part162
variable {ι : Type} [Fintype ι]

noncomputable def inverseRadius8 (d : ℕ) : ℝ :=
  (((d : ℝ) - 2) * ((d : ℝ) - 4) * ((d : ℝ) - 6) * ((d : ℝ) - 8))⁻¹

theorem trunc_invRad_eight [Nonempty ι] (hq : 8 < Fintype.card ι) (ε : ℝ) :
    (∫ Z, (if ε < radF53 Z then (radF53 Z ^ 8)⁻¹ else 0) ∂stdGauss ι) ≤
      inverseRadius8 (Fintype.card ι) := by
  set k := Fintype.card ι with hk
  have hk1 : 1 ≤ k := Fintype.card_pos
  set K := gaussianRadialFactor ι
  have hK : 0 ≤ K := gaussianRadialFactor_nonneg ι
  set Fe : ℝ → ℝ := fun r => if ε < r then (r ^ (2 * 4))⁻¹ else 0 with hFe
  have hF := gaussian_radius_integral ι Fe
  have h1 := gaussian_radius_integral ι (fun _ => (1 : ℝ))
  beta_reduce at h1
  -- the radial integrals in `rpow` form
  have hkR : (2 * 4 : ℝ) < k := by exact_mod_cast hq
  set J₀ := ∫ r in Ioi (0 : ℝ), r ^ ((k : ℝ) - 1) * Real.exp (-(1 / 2) * r ^ (2 : ℝ))
  set J₁ := ∫ r in Ioi (0 : ℝ), r ^ ((k : ℝ) - 1 - 2 * 4) * Real.exp (-(1 / 2) * r ^ (2 : ℝ))
  have eJ₀ : ∫ r in Ioi (0 : ℝ), r ^ (k - 1) * Real.exp (-r ^ 2 / 2) = J₀ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    rw [show ((k : ℝ) - 1) = ((k - 1 : ℕ) : ℝ) by rw [Nat.cast_sub hk1]; simp, Real.rpow_natCast,
      show r ^ (2 : ℝ) = r ^ 2 by norm_cast]
    ring_nf
  have hJ₀ : J₀ = (1 / 2 : ℝ) ^ (-((k : ℝ) - 1 + 1) / 2) * (1 / 2) * Real.Gamma (((k : ℝ) - 1 + 1) / 2) :=
    gamma_int _ (by linarith [(by exact_mod_cast hk1 : (1 : ℝ) ≤ k)])
  have hJ₁ : J₁ = (1 / 2 : ℝ) ^ (-((k : ℝ) - 1 - 2 * 4 + 1) / 2) * (1 / 2) *
      Real.Gamma (((k : ℝ) - 1 - 2 * 4 + 1) / 2) := gamma_int _ (by linarith)
  -- the truncated integrand is below the full one
  have hle : ∫ r in Ioi (0 : ℝ), r ^ (k - 1) * Real.exp (-r ^ 2 / 2) * Fe r ≤ J₁ := by
    have iJ₁ : IntegrableOn (fun r : ℝ => r ^ ((k : ℝ) - 1 - 2 * 4) * Real.exp (-(1 / 2) * r ^ (2 : ℝ)))
        (Ioi 0) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 2) (s := (k : ℝ) - 1 - 2 * 4)
        (b := 1 / 2) (by linarith) (by norm_num) (by norm_num)
      exact this
    have hpt : ∀ r ∈ Ioi (0 : ℝ), r ^ (k - 1) * Real.exp (-r ^ 2 / 2) * Fe r ≤
        r ^ ((k : ℝ) - 1 - 2 * 4) * Real.exp (-(1 / 2) * r ^ (2 : ℝ)) := fun r hr => by
      have hr0 : 0 < r := hr
      have he : r ^ ((k : ℝ) - 1 - 2 * 4) * Real.exp (-(1 / 2) * r ^ (2 : ℝ)) =
          r ^ (k - 1) * Real.exp (-r ^ 2 / 2) * (r ^ (2 * 4))⁻¹ := by
        rw [Real.rpow_sub hr0, Real.rpow_sub hr0, Real.rpow_one,
          show r ^ (2 : ℝ) = r ^ 2 by norm_cast,
          show r ^ ((2 : ℝ) * 4) = r ^ (2 * 4) by rw [← Real.rpow_natCast]; push_cast; ring_nf,
          Real.rpow_natCast]
        rw [show r ^ (k - 1) = r ^ k / r by
          rw [eq_div_iff hr0.ne', ← pow_succ, Nat.sub_add_cancel hk1]]
        field_simp
      rw [he]
      simp only [hFe]
      split_ifs
      · exact le_rfl
      · have : 0 ≤ r ^ (k - 1) * Real.exp (-r ^ 2 / 2) * (r ^ (2 * 4))⁻¹ := by positivity
        simpa using this
    have iL : IntegrableOn (fun r => r ^ (k - 1) * Real.exp (-r ^ 2 / 2) * Fe r) (Ioi 0) := by
      refine iJ₁.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
      · refine Measurable.aestronglyMeasurable ?_
        refine ((measurable_id.pow_const _).mul (by fun_prop)).mul ?_
        simp only [hFe]
        exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
          ((measurable_id.pow_const _).inv) measurable_const
      · rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact hpt r hr
        · have hr0 : 0 < r := hr
          simp only [hFe]
          split_ifs <;> positivity
    exact setIntegral_mono_on iL iJ₁ measurableSet_Ioi hpt
  -- assemble
  have hE : ∫ Z, Fe (√(∑ i, Z i ^ 2)) ∂stdGauss ι ≤ K * J₁ := by
    rw [hF]; exact mul_le_mul_of_nonneg_left hle hK
  have hKJ : K * J₀ = 1 := by
    rw [← eJ₀]
    have e1 : ∫ _Z, (1 : ℝ) ∂stdGauss ι = 1 := by simp
    have e2 : ∫ r in Ioi (0 : ℝ), r ^ (k - 1) * Real.exp (-r ^ 2 / 2) * 1 =
        ∫ r in Ioi (0 : ℝ), r ^ (k - 1) * Real.exp (-r ^ 2 / 2) := by simp
    rw [e1, e2] at h1
    exact h1.symm
  set a := ((k : ℝ) - 2 * 4) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hJ₁' : J₁ = (1 / 2 : ℝ) ^ (-a) * (1 / 2) * Real.Gamma a := by
    rw [hJ₁]; congr 2 <;> [congr 1; skip] <;> rw [ha] <;> ring
  have hJ₀' : J₀ = (1 / 2 : ℝ) ^ (-(a + 4)) * (1 / 2) * Real.Gamma (a + 4) := by
    rw [hJ₀]; congr 2 <;> [congr 1; skip] <;> rw [ha] <;> ring
  have hg := Real.Gamma_pos_of_pos ha0
  have hgq := Real.Gamma_pos_of_pos (by positivity : 0 < a + 4)
  have hJ₀p : 0 < J₀ := by rw [hJ₀']; positivity
  have hKe : K = 1 / J₀ := by field_simp; linarith
  have hratio : K * J₁ = (2 : ℝ)⁻¹ ^ 4 * (Real.Gamma a / Real.Gamma (a + 4)) := by
    rw [hKe, hJ₁', hJ₀']
    have h2 : (1 / 2 : ℝ) ^ (-a) = (1 / 2 : ℝ) ^ (-(a + 4)) * (2 : ℝ)⁻¹ ^ 4 := by
      rw [show (2 : ℝ)⁻¹ ^ 4 = (1 / 2 : ℝ) ^ (4 : ℝ) by norm_num,
        ← Real.rpow_add (by norm_num)]
      congr 1; ring
    rw [h2]
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ (-(a + 4)) := by positivity
    field_simp
  have hg4 : Real.Gamma (a + 4) = (a + 3) * (a + 2) * (a + 1) * a * Real.Gamma a := by
    rw [show a + 4 = (a + 3) + 1 by ring, Real.Gamma_add_one (by positivity),
      show a + 3 = (a + 2) + 1 by ring, Real.Gamma_add_one (by positivity),
      show a + 2 = (a + 1) + 1 by ring, Real.Gamma_add_one (by positivity),
      Real.Gamma_add_one ha0.ne']
    ring
  have he2 : (k : ℝ) - 2 = 2 * (a + 3) := by rw [ha]; ring
  have he4 : (k : ℝ) - 4 = 2 * (a + 2) := by rw [ha]; ring
  have he6 : (k : ℝ) - 6 = 2 * (a + 1) := by rw [ha]; ring
  have he8 : (k : ℝ) - 8 = 2 * a := by rw [ha]; ring
  calc
    _ ≤ K * J₁ := hE
    _ = (2 : ℝ)⁻¹ ^ 4 * (Real.Gamma a / Real.Gamma (a + 4)) := hratio
    _ = inverseRadius8 (Fintype.card ι) := by
      change _ = (((k : ℝ) - 2) * ((k : ℝ) - 4) * ((k : ℝ) - 6) * ((k : ℝ) - 8))⁻¹
      rw [hg4, he2, he4, he6, he8]
      have h1 : a + 1 ≠ 0 := ne_of_gt (by positivity)
      have h2 : a + 2 ≠ 0 := ne_of_gt (by positivity)
      have h3 : a + 3 ≠ 0 := ne_of_gt (by positivity)
      field_simp [ha0.ne', hg.ne']
      <;> ring

lemma inverseRadius8_pos {d : ℕ} (hd : 8 < d) : 0 < inverseRadius8 d := by
  have hdR : (8 : ℝ) < d := by exact_mod_cast hd
  unfold inverseRadius8
  exact inv_pos.mpr (mul_pos (mul_pos (mul_pos (by linarith) (by linarith))
    (by linarith)) (by linarith))

noncomputable def radiusFactor8 (d : ℕ) : ℝ := inverseRadius8 d ^ ((8 : ℝ)⁻¹)

lemma inverseRadius8_latitude {n : ℕ} (hn : 1 ≤ n) :
    inverseRadius8 (n - 1) =
      (((n : ℝ) - 3) * ((n : ℝ) - 5) * ((n : ℝ) - 7) * ((n : ℝ) - 9))⁻¹ := by
  unfold inverseRadius8
  rw [Nat.cast_sub hn, Nat.cast_one]
  congr 1 <;> ring

lemma radiusFactor8_pow {d : ℕ} (hd : 8 < d) :
    radiusFactor8 d ^ 8 = inverseRadius8 d := by
  exact Real.rpow_inv_natCast_pow (inverseRadius8_pos hd).le (by norm_num : (8 : ℕ) ≠ 0)

#print axioms trunc_invRad_eight
#print axioms radiusFactor8_pow
end BstLean.Part223
