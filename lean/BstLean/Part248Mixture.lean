import BstLean.Part248Deficit
import BstLean.Part242SY2

/-! The mixture deficit adds conditional mean loss and variance on the same distribution. -/
namespace BstLean.Part248
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part242

variable {A V : Type*} [MeasurableSpace A] [MeasurableSpace V]

theorem z_norm_order {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (hmass : μ univ ≤ 1) {q : ℕ} (hq : 1 ≤ q) (hq32 : q ≤ 32)
    {z w : X → ℝ} (mz : Measurable z) (hz0 : ∀ x, 0 ≤ z x)
    (hsq : ∀ x, z x ^ 2 ≤ w x) {H : ℝ}
    (hen : LBound μ 32 (fun x => |sqrt (w x) - 1|) H) :
    LBound μ q z (1 + H) := by
  have he := hen.lower (by exact_mod_cast (by omega : q ≠ 0)) (by norm_num)
    (by exact_mod_cast hq32 : (q : ℝ≥0∞) ≤ 32) hmass
  have hc := LBound.const (μ := μ) (k := q) (by omega) hmass (by norm_num : (0 : ℝ) ≤ 1)
  apply (hc.add (by exact_mod_cast hq) he).mono mz
  exact Filter.Eventually.of_forall fun x => by
    have hs := sqrt_le_sqrt (hsq x)
    rw [sqrt_sq (hz0 x)] at hs
    have ha := le_abs_self (sqrt (w x) - 1)
    rw [abs_of_nonneg (hz0 x), abs_of_nonneg (by positivity)]
    linarith

theorem squareSD_orders (ρ : Measure A) (ν : Measure V) [SFinite ρ]
    [IsProbabilityMeasure ν] {p : ℕ} (hp : 1 ≤ p) (he : Even p)
    {z : A × V → ℝ} {B τ M : ℝ} (hM : ∀ a v, |z (a, v)| ≤ M)
    (hz : LBound (ρ.prod ν) ((4 * p : ℕ) : ℝ≥0∞) z B)
    (hc : LBound (ρ.prod ν) ((4 * p : ℕ) : ℝ≥0∞)
      (fun q => z q - latitudeMean ν z q.1) τ) :
    LBound ρ ((2 * p : ℕ) : ℝ≥0∞) (squareSD ν z) (2 * B * τ) := by
  haveI : ENNReal.HolderTriple ((4 * p : ℕ) : ℝ≥0∞)
      ((4 * p : ℕ) : ℝ≥0∞) ((2 * p : ℕ) : ℝ≥0∞) := by
    constructor
    have hp0 : p ≠ 0 := by omega
    apply (ENNReal.toReal_eq_toReal_iff' (by simp [hp0]) (by simp [hp0])).mp
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    rw [ENNReal.toReal_add (by simp [hp0]) (by simp [hp0])]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    push_cast
    field_simp
    <;> ring
  have meanB := conditional_moment ρ ν (show Even (4 * p) from ⟨2 * p, by omega⟩)
    (hz.toMoment (by omega)) hM
  have meanLift := LBound.ofMoment (by omega : 4 * p ≠ 0) (lift_moment ρ ν meanB)
  have hplus : LBound (ρ.prod ν) ((4 * p : ℕ) : ℝ≥0∞)
      (fun q => z q + latitudeMean ν z q.1) (2 * B) := by
    convert hz.add (by exact_mod_cast (show 1 ≤ 4 * p by omega)) meanLift using 1
    ring
  have hh : LBound (ρ.prod ν) ((2 * p : ℕ) : ℝ≥0∞)
      (fun q => z q ^ 2 - latitudeMean ν z q.1 ^ 2) (2 * B * τ) := by
    convert hc.mul (r := ((2 * p : ℕ) : ℝ≥0∞)) hplus using 1
    · funext q; ring
    · ring
  have meanAbs : ∀ a, |latitudeMean ν z a| ≤ M := fun a => by
    have h := norm_integral_le_of_norm_le_const (μ := ν) (f := fun v => z (a, v))
      (C := M) (Filter.Eventually.of_forall fun v => by
        simpa only [Real.norm_eq_abs] using hM a v)
    simpa only [latitudeMean, Real.norm_eq_abs, probReal_univ, one_mul, mul_one] using h
  have hdiffB : ∀ a v, |z (a, v) ^ 2 - latitudeMean ν z a ^ 2| ≤ 2 * M ^ 2 := by
    intro a v
    have h1 : |z (a, v) ^ 2| ≤ M ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM a v) 2
    have h2 : |latitudeMean ν z a ^ 2| ≤ M ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (meanAbs a) 2
    exact (abs_sub _ _).trans (by linarith)
  have hpow : BstLean.Part223.MomentBound (ρ.prod ν) p
      (fun q => (z q ^ 2 - latitudeMean ν z q.1 ^ 2) ^ 2) ((2 * B * τ) ^ 2) := by
    apply BstLean.Part223.MomentBound.power (k := p) (r := 2)
    simpa only [Nat.mul_comm] using hh.toMoment (by omega : 2 * p ≠ 0)
  have hmean2 := conditional_moment ρ ν he hpow
    (fun a v => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hdiffB a v) 2)
  have hsqrt := hmean2.sqrt (fun a => integral_nonneg fun v => sq_nonneg _)
  have hB : 0 ≤ 2 * B * τ := by have := hz.nonneg; have := hc.nonneg; positivity
  have hsqrt' : LBound ρ ((2 * p : ℕ) : ℝ≥0∞)
      (fun a => sqrt (latitudeMean ν
        (fun q => (z q ^ 2 - latitudeMean ν z q.1 ^ 2) ^ 2) a)) (2 * B * τ) := by
    simpa only [sqrt_sq hB] using LBound.ofMoment (by omega : 2 * p ≠ 0) hsqrt
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

/-- This transfer applies at each deficit order. The loss uses the complete conditional
standard deviation and variance, with no independence assumption. -/
theorem mixture_deficit {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {q : ℕ} (hq : 1 ≤ q) {Y Z sd var : X → ℝ} (mZ : Measurable Z)
    {Y0 Xq η S Vbound : ℝ}
    (hbase : LBound μ q (fun x => max 0 (Y0 - Y x)) Xq)
    (hsd : LBound μ q sd S) (hvar : LBound μ q var Vbound)
    (hloss : ∀ᵐ x ∂μ, Y x - Z x ≤ sqrt (η / (1 - η)) * |sd x| +
      |var x| / (1 - η)) (hη1 : η < 1) :
    LBound μ q (fun x => max 0 (Y0 - Z x))
      (Xq + sqrt (η / (1 - η)) * S + Vbound / (1 - η)) := by
  have hq0 : q ≠ 0 := by omega
  have ha := hsd.mono hsd.measurable.abs (Filter.Eventually.of_forall fun x => by simp)
  have hb := hvar.mono hvar.measurable.abs (Filter.Eventually.of_forall fun x => by simp)
  have hs := ha.scale hq0 (sqrt_nonneg (η / (1 - η)))
  have hv := hb.scale hq0 (show 0 ≤ (1 - η)⁻¹ by positivity)
  have hsum := (hbase.add (by exact_mod_cast hq) hs).add (by exact_mod_cast hq) hv
  have hsum' : LBound μ q
      (fun x => max 0 (Y0 - Y x) + sqrt (η / (1 - η)) * |sd x| +
        (1 - η)⁻¹ * |var x|)
      (Xq + sqrt (η / (1 - η)) * S + Vbound / (1 - η)) := by
    simpa only [div_eq_mul_inv, mul_comm Vbound] using hsum
  apply hsum'.mono (measurable_const.max (measurable_const.sub mZ))
  filter_upwards [hloss] with x h
  rw [abs_of_nonneg (le_max_left _ _), abs_of_nonneg (by positivity)]
  apply max_le (by positivity)
  change Y0 - Z x ≤ _
  simp only [div_eq_mul_inv] at h ⊢
  have hm := le_max_right (0 : ℝ) (Y0 - Y x)
  nlinarith

/-- The mixture deficit uses the actual normalized good transverse mean.
Only kept indices require a good-mass lower bound. -/
theorem mixture_conditional (ρ : Measure A) (ν : Measure V) [SFinite ρ]
    [IsProbabilityMeasure ν] {p : ℕ} (hp : 1 ≤ p) (he : Even p)
    {K : Set A} (hK : MeasurableSet K) {G : Set (A × V)} (hG : MeasurableSet G)
    {z : A × V → ℝ} {M Y0 Xq η H τ Vbound : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hgood : ∀ a ∈ K, 1 - η ≤ ν.real {v | (a, v) ∈ G})
    (hM : ∀ a v, |z (a, v)| ≤ M)
    (hz : LBound (ρ.prod ν) ((4 * p : ℕ) : ℝ≥0∞) z (1 + H))
    (hc : LBound (ρ.prod ν) ((4 * p : ℕ) : ℝ≥0∞)
      (fun q => z q - latitudeMean ν z q.1) τ)
    (hvar : LBound ρ ((2 * p : ℕ) : ℝ≥0∞)
      (fun a => conditionalVariance ν (fun v => z (a, v))) Vbound)
    (hbase : LBound ρ ((2 * p : ℕ) : ℝ≥0∞)
      (fun a => max 0 (Y0 - latitudeMean ν (fun q => z q ^ 2) a)) Xq) :
    LBound (ρ.restrict K) ((2 * p : ℕ) : ℝ≥0∞)
      (fun a => max 0 (Y0 - goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v))))
      (Xq + sqrt (η / (1 - η)) * (2 * (1 + H) * τ) + Vbound / (1 - η)) := by
  have hsd := squareSD_orders ρ ν hp he hM hz hc
  have mz : Measurable
      (fun a => goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v))) := by
    have eq : (fun a => goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v))) =
        fun a => BstLean.Part161.goodMean ν G z a ^ 2 := by
      funext a
      exact BstLean.Part242.goodMeanSq_eq_goodMean ν hG a
    rw [eq]
    exact (BstLean.Part161.measurable_goodMean ν hG hz.measurable).pow_const 2
  apply mixture_deficit (ρ.restrict K) (q := 2 * p) (by omega) mz
    (hbase.restrict K) (hsd.restrict K) (hvar.restrict K) ?_ hη1
  apply (ae_restrict_iff' hK).mpr
  apply Filter.Eventually.of_forall
  intro a ha
  have h := good_scale_loss ν (hG.preimage measurable_prodMk_left) hη0 hη1 (hgood a ha)
    (hz.measurable.comp measurable_prodMk_left) (hM a)
  have hv0 : 0 ≤ conditionalVariance ν (fun v => z (a, v)) :=
    integral_nonneg fun v => sq_nonneg _
  simpa only [squareSD, latitudeMean, Function.comp_def, Set.preimage,
    abs_of_nonneg (sqrt_nonneg _), abs_of_nonneg hv0] using h

#print axioms squareSD_orders
#print axioms z_norm_order
#print axioms mixture_deficit
#print axioms mixture_conditional
end BstLean.Part248
