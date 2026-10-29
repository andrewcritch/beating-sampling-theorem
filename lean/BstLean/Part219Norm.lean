import BstLean.Part219Pointwise

/-! Finite input norms supply the integrability in the directional interface. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part29 (stdGauss)

lemma eLpNorm_mul_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (p : ℝ≥0∞) {a : ℝ} (ha : 0 ≤ a) :
    eLpNorm (fun x => a * f x) p μ = ENNReal.ofReal a * eLpNorm f p μ := by
  rw [show (fun x => a * f x) = a • f from rfl, eLpNorm_const_smul,
    Real.enorm_eq_ofReal_abs, abs_of_nonneg ha]

/-- A bound for the scaled gradient gives the actual moment and its integrability. -/
theorem gradient_moment_of_norm {n : ℕ} (hn : 1 ≤ n) (f : (Fin n → ℝ) → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm (fun x => √(n : ℝ) * √(BstLean.Part151.gradSq f x)) 24
      (stdGauss (Fin n)) ≤ ENNReal.ofReal C) :
    Integrable (fun x => BstLean.Part151.gradSq f x ^ 12) (stdGauss (Fin n)) ∧
      ∫ x, BstLean.Part151.gradSq f x ^ 12 ∂stdGauss (Fin n) ≤
        (C ^ 2 / n) ^ 12 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < √(n : ℝ) := sqrt_pos.mpr hnR
  let g := fun x => √(BstLean.Part151.gradSq f x)
  have hm : Measurable g := (BstLean.Part151.measurable_gradSq f).sqrt
  have he : g = fun x => (√(n : ℝ))⁻¹ * (√(n : ℝ) * g x) := by
    funext x
    rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  have hb : eLpNorm g 24 (stdGauss (Fin n)) ≤ ENNReal.ofReal (C / √(n : ℝ)) := by
    calc
      _ = ENNReal.ofReal ((√(n : ℝ))⁻¹) *
          eLpNorm (fun x => √(n : ℝ) * g x) 24 (stdGauss (Fin n)) := by
        conv_lhs => rw [he]
        exact eLpNorm_mul_nonneg _ _ _ (by positivity)
      _ ≤ ENNReal.ofReal ((√(n : ℝ))⁻¹) * ENNReal.ofReal C := mul_le_mul_right h _
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hmem : MemLp g (24 : ℝ≥0∞) (stdGauss (Fin n)) := hb.trans_lt ENNReal.ofReal_lt_top
  have hp : ∀ x, ‖g x‖ ^ 24 = BstLean.Part151.gradSq f x ^ 12 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _)]
    change (√(BstLean.Part151.gradSq f x)) ^ (2 * 12) = _
    rw [pow_mul, sq_sqrt (BstLean.Part151.gradSq_nonneg _ _)]
  have hi := hmem.integrable_norm_pow (by norm_num : (24 : ℕ) ≠ 0)
  simp_rw [hp] at hi
  refine ⟨hi, ?_⟩
  have hlp : lpNorm g 24 (stdGauss (Fin n)) ≤ C / √(n : ℝ) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hb
  have hh := pow_le_pow_left₀ lpNorm_nonneg hlp 24
  have hpow := lpNorm_nat_pow (μ := stdGauss (Fin n))
    (by norm_num : (24 : ℕ) ≠ 0) hm.aestronglyMeasurable
  norm_num only [Nat.cast_ofNat] at hpow
  rw [hpow] at hh
  have hi' : (∫ x, |g x| ^ 24 ∂stdGauss (Fin n)) =
      ∫ x, BstLean.Part151.gradSq f x ^ 12 ∂stdGauss (Fin n) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hp x
  rw [hi'] at hh
  have he' : (C / √(n : ℝ)) ^ 24 = (C ^ 2 / n) ^ 12 := by
    calc
      _ = ((C / √(n : ℝ)) ^ 2) ^ 12 := by rw [← pow_mul]
      _ = _ := by rw [div_pow, sq_sqrt hnR.le]
  exact hh.trans_eq he'

/-- Three input-norm allowances suffice, with the full-centre error used once. -/
theorem directional_norm_assembly {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (a : AgentPair n)
    (b : Fin (mA n) → ℝ) {e ξhp I E O : ℝ}
    (he : 0 < e) (hξ : 0 ≤ ξhp) (hI : 0 ≤ I) (hE : 0 ≤ E) (hO : 0 ≤ O)
    (hb : (n : ℝ) * e ≤ normSq b)
    (hfull : normSq (hid2Mean_cr a.1 a.2 c τ - b) ≤ ξhp)
    (hi : eLpNorm (idealSize c τ) 24 (stdGauss (Fin n)) ≤ ENNReal.ofReal I)
    (herr : eLpNorm (errorSize c τ a) 24 (stdGauss (Fin n)) ≤ ENNReal.ofReal E)
    (hop : eLpNorm (operatorSize c τ a) 24 (stdGauss (Fin n)) ≤ ENNReal.ofReal O) :
    eLpNorm (fun x => √(n : ℝ) *
      √(BstLean.Part151.gradSq (computedCoordinate a.1 a.2 c τ b) x)) 24
      (stdGauss (Fin n)) ≤
        ENNReal.ofReal ((√(n : ℝ) / √e) * I + (√(n : ℝ) / √e) * E +
          √(ξhp / ((n : ℝ) * e)) * O) := by
  let k := √(n : ℝ) / √e
  let r := √(ξhp / ((n : ℝ) * e))
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hr : 0 ≤ r := sqrt_nonneg _
  have hi' : eLpNorm (fun x => k * idealSize c τ x) 24 (stdGauss (Fin n)) ≤
      ENNReal.ofReal (k * I) := by
    rw [eLpNorm_mul_nonneg _ _ _ hk, ENNReal.ofReal_mul hk]
    exact mul_le_mul_right hi _
  have he' : eLpNorm (fun x => k * errorSize c τ a x) 24 (stdGauss (Fin n)) ≤
      ENNReal.ofReal (k * E) := by
    rw [eLpNorm_mul_nonneg _ _ _ hk, ENNReal.ofReal_mul hk]
    exact mul_le_mul_right herr _
  have ho' : eLpNorm (fun x => r * operatorSize c τ a x) 24 (stdGauss (Fin n)) ≤
      ENNReal.ofReal (r * O) := by
    rw [eLpNorm_mul_nonneg _ _ _ hr, ENNReal.ofReal_mul hr]
    exact mul_le_mul_right hop _
  have hm : AEStronglyMeasurable (fun x => √(n : ℝ) *
      √(BstLean.Part151.gradSq (computedCoordinate a.1 a.2 c τ b) x))
      (stdGauss (Fin n)) :=
    (measurable_const.mul (BstLean.Part151.measurable_gradSq _).sqrt).aestronglyMeasurable
  have hd := eLpNorm_mono_ae_real (p := (24 : ℝ≥0∞)) hm
    ((gradient_three_terms hn c hτ a b he hξ hb hfull).mono fun x hx => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ √(n : ℝ) * √(BstLean.Part151.gradSq _ x))] using hx)
  refine hd.trans ?_
  have hadd := eLpNorm_add_le (μ := stdGauss (Fin n)) (p := (24 : ℝ≥0∞))
    (f := (fun x => k * idealSize c τ x) + (fun x => k * errorSize c τ a x))
    (g := fun x => r * operatorSize c τ a x) (by norm_num)
  have hadd' := eLpNorm_add_le (μ := stdGauss (Fin n)) (p := (24 : ℝ≥0∞))
    (f := fun x => k * idealSize c τ x) (g := fun x => k * errorSize c τ a x)
    (by norm_num)
  have hh := hadd.trans (add_le_add (hadd'.trans (add_le_add hi' he')) ho')
  simp only [← ENNReal.ofReal_add (mul_nonneg hk hI) (mul_nonneg hk hE),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hk hI) (mul_nonneg hk hE))
      (mul_nonneg hr hO)] at hh
  exact hh

#print axioms gradient_moment_of_norm
#print axioms directional_norm_assembly
end BstLean.Part219
