import BstLean.Part242Reciprocal

/-! The SY deficit follows from the full input energy and location moments. -/
namespace BstLean.Part242
open MeasureTheory Real Set
open scoped ENNReal

lemma energy_deficit {w : ℝ} (hw : 0 ≤ w) : 1 - w ≤ 2 * |sqrt w - 1| := by
  have hs := sq_sqrt hw
  have ha := le_abs_self (1 - sqrt w)
  rw [abs_sub_comm] at ha
  nlinarith [sq_nonneg (sqrt w - 1)]

variable {A V : Type*} [MeasurableSpace A] [MeasurableSpace V]

theorem conditional_deficit (ρ : Measure A) (ν : Measure V) [SFinite ρ]
    [IsProbabilityMeasure ν] (hmass : ρ univ ≤ 1)
    {f w : A × V → ℝ} {m μ0 g H Mf Mw : ℝ}
    (mf : Measurable f) (mw : Measurable w) (hμ : |m| ≤ μ0)
    (hfB : ∀ a v, |f (a, v)| ≤ Mf)
    (hw0 : ∀ q, 0 ≤ w q) (hwB : ∀ a v, w (a, v) ≤ Mw)
    (hdev : LBound (ρ.prod ν) 8 (fun q => f q - m) g)
    (hen : LBound (ρ.prod ν) 4 (fun q => |sqrt (w q) - 1|) H) :
    LBound ρ 4
      (fun a => max 0 ((1 - μ0 ^ 2) -
        (latitudeMean ν w a - latitudeMean ν (fun q => f q ^ 2) a)))
      (2 * H + g * (2 * μ0 + g)) := by
  have hμ0 : 0 ≤ μ0 := (abs_nonneg _).trans hμ
  have hm : (ρ.prod ν) univ ≤ 1 := by
    rw [← univ_prod_univ, Measure.prod_prod, measure_univ (μ := ν), mul_one]
    exact hmass
  have hc0 := LBound.const (μ := ρ.prod ν) (by norm_num : (8 : ℕ) ≠ 0)
    hm (show 0 ≤ 2 * μ0 by positivity)
  have hc : LBound (ρ.prod ν) 8 (fun _ => 2 * m) (2 * μ0) :=
    hc0.mono measurable_const (Filter.Eventually.of_forall fun q => by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * μ0)]
      exact mul_le_mul_of_nonneg_left hμ (by norm_num))
  have hplus : LBound (ρ.prod ν) 8 (fun q => f q + m) (2 * μ0 + g) := by
    convert hc.add (by norm_num) hdev using 1
    funext q
    ring
  have hp : LBound (ρ.prod ν) 4 (fun q => (f q - m) * (f q + m))
      (g * (2 * μ0 + g)) := hdev.mul hplus
  have hpabs := hp.mono (hp.measurable.abs)
    (Filter.Eventually.of_forall fun q => by simp)
  let b : A × V → ℝ := fun q => 2 * |sqrt (w q) - 1| + |(f q - m) * (f q + m)|
  have hb : LBound (ρ.prod ν) 4 b (2 * H + g * (2 * μ0 + g)) :=
    (hen.scale (by norm_num : (4 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 2)).add
      (by norm_num) hpabs
  have b0 : ∀ q, 0 ≤ b q := fun q => by dsimp [b]; positivity
  have bB : ∀ a v, |b (a, v)| ≤
      2 * (sqrt Mw + 1) + (Mf + |m|) ^ 2 := by
    intro a v
    have h1 : |sqrt (w (a, v)) - 1| ≤ sqrt Mw + 1 := by
      have h := abs_sub (sqrt (w (a, v))) 1
      rw [abs_of_nonneg (sqrt_nonneg _), abs_one] at h
      exact h.trans (add_le_add (sqrt_le_sqrt (hwB a v)) le_rfl)
    have h2 : |f (a, v) - m| ≤ Mf + |m| :=
      (abs_sub _ _).trans (add_le_add (hfB a v) le_rfl)
    have h3 : |f (a, v) + m| ≤ Mf + |m| :=
      (abs_add_le _ _).trans (add_le_add (hfB a v) le_rfl)
    rw [abs_of_nonneg (b0 _)]
    dsimp [b]
    rw [abs_mul]
    have hh := mul_le_mul h2 h3 (abs_nonneg _) ((abs_nonneg _).trans h2)
    nlinarith
  have hmean : LBound ρ 4 (latitudeMean ν b) (2 * H + g * (2 * μ0 + g)) := by
    simpa only [Nat.cast_ofNat] using LBound.ofMoment (by norm_num : (4 : ℕ) ≠ 0)
      (conditional_moment ρ ν (by decide : Even 4) (hb.toMoment (by norm_num)) bB)
  have mb := measurable_latitudeMean ν hb.measurable
  have my : Measurable (fun a => (1 - μ0 ^ 2) -
      (latitudeMean ν w a - latitudeMean ν (fun q => f q ^ 2) a)) :=
    measurable_const.sub
      ((measurable_latitudeMean ν mw).sub (measurable_latitudeMean ν (mf.pow_const 2)))
  apply hmean.mono (g := fun a => max 0 ((1 - μ0 ^ 2) -
    (latitudeMean ν w a - latitudeMean ν (fun q => f q ^ 2) a))) (measurable_const.max my)
  apply Filter.Eventually.of_forall
  intro a
  have mfA : Measurable (fun v => f (a, v)) :=
    mf.comp ((measurable_const (a := a)).prodMk measurable_id)
  have mwA : Measurable (fun v => w (a, v)) :=
    mw.comp ((measurable_const (a := a)).prodMk measurable_id)
  have iw : Integrable (fun v => w (a, v)) ν :=
    BstLean.Part162.intB mwA (fun v => by
      rw [abs_of_nonneg (hw0 _)]; exact hwB a v)
  have if2 : Integrable (fun v => f (a, v) ^ 2) ν :=
    BstLean.Part162.intB (mfA.pow_const 2) (fun v => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hfB a v) 2)
  have ib : Integrable (fun v => b (a, v)) ν :=
    BstLean.Part162.intB
      (hb.measurable.comp (measurable_const.prodMk measurable_id)) (bB a)
  have hpoint : ∀ v, (1 - μ0 ^ 2) - (w (a, v) - f (a, v) ^ 2) ≤ b (a, v) := by
    intro v
    have h1 := energy_deficit (hw0 (a, v))
    have h2 := le_abs_self ((f (a, v) - m) * (f (a, v) + m))
    have hm2 : m ^ 2 ≤ μ0 ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg m) hμ 2
    dsimp [b]
    nlinarith
  have hi := integral_mono ((integrable_const (1 - μ0 ^ 2)).sub (iw.sub if2)) ib hpoint
  change (∫ v, (1 - μ0 ^ 2) - (w (a, v) - f (a, v) ^ 2) ∂ν) ≤
    ∫ v, b (a, v) ∂ν at hi
  rw [integral_sub (μ := ν) (f := fun _ : V => 1 - μ0 ^ 2)
    (g := fun v => w (a, v) - f (a, v) ^ 2)
    (integrable_const (1 - μ0 ^ 2)) (iw.sub if2),
    integral_sub (f := fun v => w (a, v)) (g := fun v => f (a, v) ^ 2) iw if2] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  have hb0 : 0 ≤ latitudeMean ν b a := integral_nonneg fun v => b0 _
  rw [abs_of_nonneg (le_max_left _ _), abs_of_nonneg hb0]
  exact max_le hb0 hi

end BstLean.Part242
