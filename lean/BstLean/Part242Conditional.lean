import BstLean.Part242Norm
import BstLean.Part162Sc
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-! Conditional means integrate the complete transverse distribution first. -/
namespace BstLean.Part242
open MeasureTheory Real Set
open scoped ENNReal

variable {A V : Type*} [MeasurableSpace A] [MeasurableSpace V]

noncomputable def latitudeMean (ν : Measure V) (f : A × V → ℝ) (a : A) : ℝ :=
  ∫ v, f (a, v) ∂ν

lemma measurable_latitudeMean (ν : Measure V) [SFinite ν] {f : A × V → ℝ}
    (hf : Measurable f) : Measurable (latitudeMean ν f) :=
  hf.stronglyMeasurable.integral_prod_right'.measurable

/-- Jensen retains the complete inner probability distribution and the outer mass. -/
theorem conditional_moment (ρ : Measure A) (ν : Measure V) [SFinite ρ]
    [IsProbabilityMeasure ν] {k : ℕ} (hk : Even k) {f : A × V → ℝ} {B M : ℝ}
    (hf : BstLean.Part223.MomentBound (ρ.prod ν) k f B)
    (hM : ∀ a v, |f (a, v)| ≤ M) :
    BstLean.Part223.MomentBound ρ k (latitudeMean ν f) B := by
  have mi := measurable_latitudeMean ν hf.measurable
  have mf := fun a : A => hf.measurable.comp
    ((measurable_const (a := a)).prodMk (measurable_id (α := V)))
  have ip := fun a => BstLean.Part162.intB (μ := ν) (mf a) (hM a)
  have ik : ∀ a, Integrable (fun v => f (a, v) ^ k) ν := fun a =>
    BstLean.Part162.intB ((mf a).pow_const k) (fun v => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM a v) k)
  have j : ∀ a, |latitudeMean ν f a| ^ k ≤ ∫ v, |f (a, v)| ^ k ∂ν := by
    intro a
    have hj := hk.convexOn_pow.map_integral_le
      (continuous_pow k).continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun v => mem_univ (f (a, v))) (ip a) (ik a)
    simpa only [latitudeMean, hk.pow_abs] using hj
  refine ⟨mi, hf.nonneg, ?_⟩
  refine (lintegral_mono fun a => ENNReal.ofReal_le_ofReal (j a)).trans ?_
  have eq : ∀ a, ENNReal.ofReal (∫ v, |f (a, v)| ^ k ∂ν) =
      ∫⁻ v, ENNReal.ofReal (|f (a, v)| ^ k) ∂ν := by
    intro a
    apply ofReal_integral_eq_lintegral_ofReal
    · simpa only [hk.pow_abs] using ik a
    · exact Filter.Eventually.of_forall fun v => pow_nonneg (abs_nonneg _) k
  simp_rw [eq]
  rw [← lintegral_prod _ ((hf.measurable.abs.pow_const k).ennreal_ofReal.aemeasurable)]
  exact hf.moment

/-- FB at every positive integer order `2*p`, including the paper orders through 24. -/
theorem FB (ρ : Measure A) (ν : Measure V) [SFinite ρ] [IsProbabilityMeasure ν]
    (p : ℕ) (hp : 1 ≤ p) (hmass : ρ univ ≤ 1)
    {f : A × V → ℝ} {μ0 g M : ℝ} (hμ : 0 ≤ μ0)
    (hf : Measurable f) (hM : ∀ a v, |f (a, v)| ≤ M)
    (hc : BstLean.Part223.MomentBound (ρ.prod ν) (2 * p)
      (fun q => f q - μ0) g) :
    LBound ρ (2 * p) (latitudeMean ν f) (μ0 + g) := by
  have hk : 2 * p ≠ 0 := by omega
  have he : Even (2 * p) := ⟨p, by omega⟩
  have hm : (ρ.prod ν) univ ≤ 1 := by
    rw [← univ_prod_univ, Measure.prod_prod, measure_univ (μ := ν), mul_one]
    exact hmass
  have hconst := (LBound.const hk hm hμ).toMoment hk
  have hsum := hconst.add (by omega : 1 ≤ 2 * p) hc
  have hfull : BstLean.Part223.MomentBound (ρ.prod ν) (2 * p) f (μ0 + g) := by
    convert hsum using 1
    funext q
    ring
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    LBound.ofMoment hk (conditional_moment ρ ν he hfull hM)

/-- Restriction keeps the original outer mass. It does not normalize the kept set. -/
theorem FB_kept (ρ : Measure A) (ν : Measure V) [SFinite ρ] [IsProbabilityMeasure ν]
    (p : ℕ) (hp : 1 ≤ p) (hmass : ρ univ ≤ 1) (K : Set A)
    {f : A × V → ℝ} {μ0 g M : ℝ} (hμ : 0 ≤ μ0)
    (hf : Measurable f) (hM : ∀ a v, |f (a, v)| ≤ M)
    (hc : BstLean.Part223.MomentBound (ρ.prod ν) (2 * p)
      (fun q => f q - μ0) g) :
    LBound (ρ.restrict K) (2 * p) (latitudeMean ν f) (μ0 + g) :=
  (FB ρ ν p hp hmass hμ hf hM hc).restrict K

end BstLean.Part242
