import BstLean.Part242GoodScale

/-! Conditional centering bounds the standard deviation of the squared field. -/
namespace BstLean.Part242
open MeasureTheory Real Set
open scoped ENNReal

variable {A V : Type*} [MeasurableSpace A] [MeasurableSpace V]

/-- The energy event supplies the order-eight residual-field norm. -/
theorem z_norm_from_energy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (hmass : μ univ ≤ 1) {z w : X → ℝ} (mz : Measurable z)
    (hz0 : ∀ x, 0 ≤ z x) (hsq : ∀ x, z x ^ 2 ≤ w x) {H : ℝ}
    (hen : LBound μ 32 (fun x => |sqrt (w x) - 1|) H) :
    LBound μ 8 z (1 + H) := by
  have he8 := hen.lower (by norm_num) (by norm_num) (by norm_num : (8 : ℝ≥0∞) ≤ 32) hmass
  have hc : LBound μ 8 (fun _ => (1 : ℝ)) 1 := by
    simpa only [Nat.cast_ofNat] using LBound.const (μ := μ)
      (by norm_num : (8 : ℕ) ≠ 0) hmass (by norm_num : (0 : ℝ) ≤ 1)
  apply (hc.add (by norm_num) he8).mono mz
  exact Filter.Eventually.of_forall fun x => by
    have hs := sqrt_le_sqrt (hsq x)
    rw [sqrt_sq (hz0 x)] at hs
    have ha := le_abs_self (sqrt (w x) - 1)
    rw [abs_of_nonneg (hz0 x), abs_of_nonneg (by positivity)]
    linarith

lemma lift_moment (ρ : Measure A) (ν : Measure V) [SFinite ρ] [IsProbabilityMeasure ν]
    {k : ℕ} {f : A → ℝ} {B : ℝ} (h : BstLean.Part223.MomentBound ρ k f B) :
    BstLean.Part223.MomentBound (ρ.prod ν) k (fun q => f q.1) B := by
  refine ⟨h.measurable.comp measurable_fst, h.nonneg, ?_⟩
  rw [lintegral_prod (μ := ρ) (ν := ν)
    (fun q : A × V => ENNReal.ofReal (|f q.1| ^ k))
    ((h.measurable.comp measurable_fst).abs.pow_const k).ennreal_ofReal.aemeasurable]
  simpa only [lintegral_const, measure_univ (μ := ν), mul_one] using h.moment

noncomputable def squareSD (ν : Measure V) (z : A × V → ℝ) (a : A) : ℝ :=
  sqrt (conditionalVariance ν (fun v => z (a, v) ^ 2))

lemma measurable_squareSD (ν : Measure V) [SFinite ν] {z : A × V → ℝ}
    (mz : Measurable z) : Measurable (squareSD ν z) := by
  have mm := measurable_latitudeMean ν (mz.pow_const 2)
  exact (measurable_latitudeMean ν
    ((mz.pow_const 2).sub (mm.comp measurable_fst) |>.pow_const 2)).sqrt

theorem conditional_squareSD (ρ : Measure A) (ν : Measure V) [SFinite ρ]
    [IsProbabilityMeasure ν] {z : A × V → ℝ} {B τ M : ℝ}
    (hM : ∀ a v, |z (a, v)| ≤ M)
    (hz : LBound (ρ.prod ν) 8 z B)
    (hc : LBound (ρ.prod ν) 8 (fun q => z q - latitudeMean ν z q.1) τ) :
    LBound ρ 4 (squareSD ν z) (2 * B * τ) := by
  have meanB := conditional_moment ρ ν (by decide : Even 8) (hz.toMoment (by norm_num)) hM
  have meanLift := LBound.ofMoment (by norm_num : (8 : ℕ) ≠ 0) (lift_moment ρ ν meanB)
  have hp : LBound (ρ.prod ν) 8 (fun q => z q + latitudeMean ν z q.1) (2 * B) := by
    convert hz.add (by norm_num) meanLift using 1
    ring
  have hh : LBound (ρ.prod ν) 4 (fun q => z q ^ 2 - latitudeMean ν z q.1 ^ 2)
      (2 * B * τ) := by
    convert hc.mul (r := 4) hp using 1
    · funext q
      ring
    · ring
  have meanAbs : ∀ a, |latitudeMean ν z a| ≤ M := fun a => by
    have h := norm_integral_le_of_norm_le_const (μ := ν) (f := fun v => z (a, v))
      (C := M) (Filter.Eventually.of_forall fun v => by simpa only [Real.norm_eq_abs] using hM a v)
    simpa only [latitudeMean, Real.norm_eq_abs, probReal_univ, one_mul, mul_one] using h
  have hdiffB : ∀ a v, |z (a, v) ^ 2 - latitudeMean ν z a ^ 2| ≤ 2 * M ^ 2 := by
    intro a v
    have h1 : |z (a, v) ^ 2| ≤ M ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM a v) 2
    have h2 : |latitudeMean ν z a ^ 2| ≤ M ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (meanAbs a) 2
    exact (abs_sub _ _).trans (by linarith)
  have hpow := (hh.toMoment (by norm_num : (4 : ℕ) ≠ 0)).power (k := 2) (r := 2)
  have hmean2 := conditional_moment ρ ν (by decide : Even 2) hpow
    (fun a v => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hdiffB a v) 2)
  have hsqrt := hmean2.sqrt (fun a => integral_nonneg fun v => sq_nonneg _)
  have hB : 0 ≤ 2 * B * τ := by have := hz.nonneg; have := hc.nonneg; positivity
  have hsqrt' : LBound ρ 4
      (fun a => sqrt (latitudeMean ν
        (fun q => (z q ^ 2 - latitudeMean ν z q.1 ^ 2) ^ 2) a)) (2 * B * τ) := by
    have h := LBound.ofMoment (by norm_num : (4 : ℕ) ≠ 0) hsqrt
    simpa only [Nat.cast_mul, Nat.cast_ofNat, sqrt_sq hB] using h
  apply hsqrt'.mono (measurable_squareSD ν hz.measurable)
  apply Filter.Eventually.of_forall
  intro a
  have mzA := hz.measurable.comp ((measurable_const (a := a)).prodMk measurable_id)
  have hsqB : ∀ v, |z (a, v) ^ 2| ≤ M ^ 2 := fun v => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM a v) 2
  have hv := BstLean.Part162.var_le_sq_sub (μ := ν) (mzA.pow_const 2) hsqB
    (latitudeMean ν z a ^ 2)
  dsimp only [squareSD]
  simp only [abs_of_nonneg (sqrt_nonneg _)]
  exact sqrt_le_sqrt hv

end BstLean.Part242
