import BstLean.Part242Deficit

/-! Centred deficits retain the full inner probability distribution. -/
namespace BstLean.Part248
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part242

variable {A V : Type*} [MeasurableSpace A] [MeasurableSpace V]

lemma conditional_norm (ρ : Measure A) (ν : Measure V) [SFinite ρ]
    [IsProbabilityMeasure ν] {q : ℕ} (hq : q ≠ 0) (he : Even q)
    {f : A × V → ℝ} {B M : ℝ} (hf : LBound (ρ.prod ν) q f B)
    (hM : ∀ a v, |f (a, v)| ≤ M) : LBound ρ q (latitudeMean ν f) B :=
  LBound.ofMoment hq (conditional_moment ρ ν he (hf.toMoment hq) hM)

/-- D1 separates the conditional mean from the conditional square.
The mean input has bound `a`; the full centred input has bound `b` at order `2*q`. -/
theorem D1 (ρ : Measure A) (ν : Measure V) [SFinite ρ]
    [IsProbabilityMeasure ν] {q : ℕ} (hq : 1 ≤ q) (he : Even q)
    {f w : A × V → ℝ} {m μ0 a b H Mf Mw : ℝ}
    (mf : Measurable f) (mw : Measurable w) (hμ : |m| ≤ μ0)
    (hfB : ∀ x v, |f (x, v)| ≤ Mf)
    (hw0 : ∀ x, 0 ≤ w x) (hwB : ∀ x v, w (x, v) ≤ Mw)
    (hmean : LBound ρ q (latitudeMean ν (fun x => f x - m)) a)
    (hphi : LBound (ρ.prod ν) ((2 * q : ℕ) : ℝ≥0∞) (fun x => f x - m) b)
    (hen : LBound (ρ.prod ν) q (fun x => |sqrt (w x) - 1|) H) :
    LBound ρ q (fun x => max 0 ((1 - μ0 ^ 2) -
      (latitudeMean ν w x - latitudeMean ν (fun z => f z ^ 2) x)))
      (2 * H + 2 * μ0 * a + b ^ 2) := by
  have hq0 : q ≠ 0 := by omega
  have hμ0 : 0 ≤ μ0 := (abs_nonneg _).trans hμ
  let en : A × V → ℝ := fun x => |sqrt (w x) - 1|
  let phi : A × V → ℝ := fun x => f x - m
  have phiB : ∀ x v, |phi (x, v)| ≤ Mf + |m| := fun x v =>
    (abs_sub _ _).trans (add_le_add (hfB x v) le_rfl)
  have enB : ∀ x v, |en (x, v)| ≤ sqrt Mw + 1 := by
    intro x v
    simp only [en, abs_abs]
    have h := abs_sub (sqrt (w (x, v))) 1
    rw [abs_of_nonneg (sqrt_nonneg _), abs_one] at h
    exact h.trans (add_le_add (sqrt_le_sqrt (hwB x v)) le_rfl)
  have enN := conditional_norm ρ ν hq0 he hen enB
  have sqN : LBound (ρ.prod ν) q (fun x => phi x ^ 2) (b ^ 2) := by
    apply LBound.ofMoment hq0
    apply BstLean.Part223.MomentBound.power (k := q) (r := 2)
    simpa only [Nat.mul_comm] using hphi.toMoment (by omega : 2 * q ≠ 0)
  have sqB : ∀ x v, |phi (x, v) ^ 2| ≤ (Mf + |m|) ^ 2 := by
    intro x v
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (phiB x v) 2
  have sqMean := conditional_norm ρ ν hq0 he sqN sqB
  have meanAbs := hmean.mono hmean.measurable.abs
    (Filter.Eventually.of_forall fun x => by simp)
  have hsum := ((enN.scale hq0 (by norm_num : (0 : ℝ) ≤ 2)).add
    (by exact_mod_cast hq) (meanAbs.scale hq0 (by positivity : 0 ≤ 2 * μ0))).add
    (by exact_mod_cast hq) sqMean
  have my := (measurable_latitudeMean ν mw).sub
    (measurable_latitudeMean ν (mf.pow_const 2))
  apply hsum.mono (measurable_const.max (measurable_const.sub my))
  apply Filter.Eventually.of_forall
  intro x
  have mfX : Measurable (fun v => f (x, v)) :=
    mf.comp (measurable_const.prodMk measurable_id)
  have mwX : Measurable (fun v => w (x, v)) :=
    mw.comp (measurable_const.prodMk measurable_id)
  have iphi : Integrable (fun v => phi (x, v)) ν :=
    BstLean.Part162.intB (mfX.sub measurable_const) (phiB x)
  have isq : Integrable (fun v => phi (x, v) ^ 2) ν :=
    BstLean.Part162.intB ((mfX.sub measurable_const).pow_const 2) (sqB x)
  have ien : Integrable (fun v => en (x, v)) ν :=
    BstLean.Part162.intB ((mwX.sqrt.sub measurable_const).abs) (enB x)
  have iw : Integrable (fun v => w (x, v)) ν :=
    BstLean.Part162.intB mwX (fun v => by
      rw [abs_of_nonneg (hw0 _)]; exact hwB x v)
  have if2 : Integrable (fun v => f (x, v) ^ 2) ν :=
    BstLean.Part162.intB (mfX.pow_const 2) (fun v => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hfB x v) 2)
  have hs : (∫ v, f (x, v) ^ 2 ∂ν) = m ^ 2 +
      2 * m * latitudeMean ν phi x + latitudeMean ν (fun z => phi z ^ 2) x := by
    have eq : (fun v => f (x, v) ^ 2) =
        (fun v => m ^ 2 + 2 * m * phi (x, v) + phi (x, v) ^ 2) := by
      funext v; dsimp [phi]; ring
    rw [eq, integral_add (f := fun v => m ^ 2 + 2 * m * phi (x, v))
      (g := fun v => phi (x, v) ^ 2)
      ((integrable_const _).add (iphi.const_mul _)) isq,
      integral_add (f := fun _ => m ^ 2) (g := fun v => 2 * m * phi (x, v))
      (integrable_const _) (iphi.const_mul _), integral_const,
      integral_const_mul]
    simp [latitudeMean]
  have hew := integral_mono ((integrable_const (1 : ℝ)).sub iw)
    (ien.const_mul 2) (fun v => energy_deficit (hw0 (x, v)))
  change (∫ v, 1 - w (x, v) ∂ν) ≤ ∫ v, 2 * en (x, v) ∂ν at hew
  rw [integral_sub (f := fun _ => (1 : ℝ)) (g := fun v => w (x, v))
    (integrable_const _) iw, integral_const, integral_const_mul] at hew
  simp only [probReal_univ, smul_eq_mul, one_mul] at hew
  have hm2 : m ^ 2 ≤ μ0 ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg m) hμ 2
  have hma : m * latitudeMean ν phi x ≤ μ0 * |latitudeMean ν phi x| :=
    (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hμ (abs_nonneg _))
  have en0 : 0 ≤ latitudeMean ν en x := integral_nonneg fun v => abs_nonneg _
  have sq0 : 0 ≤ latitudeMean ν (fun z => phi z ^ 2) x :=
    integral_nonneg fun v => sq_nonneg _
  change |max 0 ((1 - μ0 ^ 2) - (latitudeMean ν w x -
    latitudeMean ν (fun z => f z ^ 2) x))| ≤
    |2 * latitudeMean ν en x + 2 * μ0 * |latitudeMean ν phi x| +
      latitudeMean ν (fun z => phi z ^ 2) x|
  rw [abs_of_nonneg (le_max_left _ _), abs_of_nonneg (by positivity)]
  apply max_le (by positivity)
  change 1 - μ0 ^ 2 - ((∫ v, w (x, v) ∂ν) - ∫ v, f (x, v) ^ 2 ∂ν) ≤ _
  rw [hs]
  change 1 - (∫ v, w (x, v) ∂ν) ≤ 2 * latitudeMean ν en x at hew
  nlinarith

/-- Conditional Jensen supplies the linear term from the full order-q moment.
At q=4,8,12, set a=c_(q/2)*s and b=c_q*s to obtain the paper formula. -/
theorem D1_from_full (ρ : Measure A) (ν : Measure V) [SFinite ρ]
    [IsProbabilityMeasure ν] {q : ℕ} (hq : 1 ≤ q) (he : Even q)
    {f w : A × V → ℝ} {m μ0 a b H Mf Mw : ℝ}
    (mf : Measurable f) (mw : Measurable w) (hμ : |m| ≤ μ0)
    (hfB : ∀ x v, |f (x, v)| ≤ Mf)
    (hw0 : ∀ x, 0 ≤ w x) (hwB : ∀ x v, w (x, v) ≤ Mw)
    (hphiQ : LBound (ρ.prod ν) q (fun x => f x - m) a)
    (hphi2Q : LBound (ρ.prod ν) ((2 * q : ℕ) : ℝ≥0∞) (fun x => f x - m) b)
    (hen : LBound (ρ.prod ν) q (fun x => |sqrt (w x) - 1|) H) :
    LBound ρ q (fun x => max 0 ((1 - μ0 ^ 2) -
      (latitudeMean ν w x - latitudeMean ν (fun z => f z ^ 2) x)))
      (2 * H + 2 * μ0 * a + b ^ 2) := by
  have hpB : ∀ x v, |f (x, v) - m| ≤ Mf + |m| := fun x v =>
    (abs_sub _ _).trans (add_le_add (hfB x v) le_rfl)
  exact D1 ρ ν hq he mf mw hμ hfB hw0 hwB
    (conditional_norm ρ ν (by omega) he hphiQ hpB) hphi2Q hen

#print axioms conditional_norm
#print axioms D1
#print axioms D1_from_full
end BstLean.Part248
