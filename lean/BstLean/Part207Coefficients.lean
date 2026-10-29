import BstLean.Part207Log
import BstLean.Part180HQ

/-! Sharp mixture coefficients for HQ. -/
namespace BstLean.Part207
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part161
open BstLean.Part180

variable {V : Type*} [MeasurableSpace V]

theorem mix_coef_bounds_sharp {n : ℕ} (pm : Measure V) [IsProbabilityMeasure pm] (c : Fin n → ℝ)
    {l0 S0 : ℝ} (hS0 : 0 < S0) {l S : V → ℝ} (hl : Measurable l) (hS : Measurable S)
    {ε₀ δ₀ : ℝ} (hε₀ : ε₀ < 1) (hwS : ∀ v, |S v / S0 - 1| ≤ ε₀) (hwl : ∀ v, |l v - l0| ≤ δ₀)
    (hml : ∫ v, (l v - l0) ∂pm = 0) (hmS : ∫ v, (S v / S0 - 1) ∂pm = 0) :
    |∫ v, (-(n / 2) * log (S v / S0) + n / 2 * (1 - 1 / (S v / S0)) -
          (l v - l0) ^ 2 * (normSq c / S0) / (2 * (S v / S0))) ∂pm| ≤
        n * (1 / (4 * (1 - ε₀) ^ 2)) * (∫ v, (S v / S0 - 1) ^ 2 ∂pm) +
          (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) / (2 * (1 - ε₀)) ∧
      (∫ v, (1 - 1 / (S v / S0)) ∂pm) ^ 2 ≤ (∫ v, (S v / S0 - 1) ^ 2 ∂pm) ^ 2 / (1 - ε₀) ^ 2 ∧
      normSq c / S0 * (∫ v, (l v - l0) / (S v / S0) ∂pm) ^ 2 ≤
        (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) * (∫ v, (S v / S0 - 1) ^ 2 ∂pm) /
          (1 - ε₀) ^ 2 := by
  have : Nonempty V := nonempty_of_isProbabilityMeasure pm
  have hε0 : 0 ≤ ε₀ := (abs_nonneg _).trans (hwS (Classical.arbitrary V))
  have hδ0 : 0 ≤ δ₀ := (abs_nonneg _).trans (hwl (Classical.arbitrary V))
  have hd : 0 < 1 - ε₀ := by linarith
  have hr1 : ∀ v, 1 - ε₀ ≤ S v / S0 := fun v => by have := (abs_le.mp (hwS v)).1; linarith
  have hrp : ∀ v, 0 < S v / S0 := fun v => lt_of_lt_of_le hd (hr1 v)
  set a2 := normSq c / S0 with ha2d
  have ha2 : 0 ≤ a2 := div_nonneg (normSq_nonneg c) hS0.le
  set x : V → ℝ := fun v => S v / S0 - 1 with hx
  set δ : V → ℝ := fun v => l v - l0 with hδ
  have mr : Measurable (fun v => S v / S0) := hS.div_const S0
  have mx : Measurable x := mr.sub_const 1
  have mδ : Measurable δ := hl.sub_const l0
  have bx : ∀ v, |x v| ≤ ε₀ := hwS
  have bδ : ∀ v, |δ v| ≤ δ₀ := hwl
  have bx2 : ∀ v, |x v ^ 2| ≤ ε₀ ^ 2 := fun v => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bx v) 2
  have bδ2 : ∀ v, |a2 * δ v ^ 2| ≤ a2 * δ₀ ^ 2 := fun v => by
    rw [abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ ha2
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bδ v) 2
  have iX : Integrable (fun v => x v ^ 2) pm := ibd pm (mx.pow_const 2) bx2
  have iY : Integrable (fun v => a2 * δ v ^ 2) pm :=
    ibd pm (measurable_const.mul (mδ.pow_const 2)) bδ2
  have er : ∀ v, S v / S0 = 1 + x v := fun v => by simp only [hx]; ring
  refine ⟨?_, ?_, ?_⟩
  · -- the constant term
    have hpt : ∀ v, |-(n / 2) * log (S v / S0) + n / 2 * (1 - 1 / (S v / S0)) -
        (l v - l0) ^ 2 * a2 / (2 * (S v / S0))| ≤
        n * (1 / (4 * (1 - ε₀) ^ 2)) * x v ^ 2 + a2 * δ v ^ 2 / (2 * (1 - ε₀)) := by
      intro v
      have e1 : -(n / 2) * log (S v / S0) + n / 2 * (1 - 1 / (S v / S0)) -
          (l v - l0) ^ 2 * a2 / (2 * (S v / S0)) =
          -(n / 2) * (log (1 + x v) - x v / (1 + x v)) - a2 * δ v ^ 2 / (2 * (1 + x v)) := by
        rw [er v]
        have : (1 + x v) ≠ 0 := by rw [← er v]; exact (hrp v).ne'
        simp only [hδ]
        field_simp
        ring
      rw [e1]
      have h1 := log_sub_frac_sharp (bx v) hε₀
      have h2 : |a2 * δ v ^ 2 / (2 * (1 + x v))| ≤ a2 * δ v ^ 2 / (2 * (1 - ε₀)) := by
        have hp : 0 < 1 + x v := by rw [← er v]; exact hrp v
        rw [abs_div, abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        have := hr1 v; rw [er v] at this; linarith
      have hn0 : (0 : ℝ) ≤ n / 2 := by positivity
      calc |-(n / 2) * (log (1 + x v) - x v / (1 + x v)) - a2 * δ v ^ 2 / (2 * (1 + x v))|
          ≤ |-(n / 2) * (log (1 + x v) - x v / (1 + x v))| + |a2 * δ v ^ 2 / (2 * (1 + x v))| :=
            abs_sub _ _
        _ ≤ n / 2 * (x v ^ 2 / (2 * (1 - ε₀) ^ 2)) + a2 * δ v ^ 2 / (2 * (1 - ε₀)) := by
            rw [abs_mul, abs_neg, abs_of_nonneg hn0]
            gcongr
        _ = _ := by field_simp; ring
    have iR : Integrable (fun v => n * (1 / (4 * (1 - ε₀) ^ 2)) * x v ^ 2 +
        a2 * δ v ^ 2 / (2 * (1 - ε₀))) pm := (iX.const_mul _).add (iY.div_const _)
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => abs_nonneg _) iR
      (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
    rw [integral_add (iX.const_mul _) (iY.div_const _), integral_const_mul, integral_div]
  · -- the coefficient of `|z|² − n`
    have hpt : ∀ v, 1 - 1 / (S v / S0) = x v - x v ^ 2 / (S v / S0) := fun v => by
      rw [er v]
      have : (1 + x v) ≠ 0 := by rw [← er v]; exact (hrp v).ne'
      field_simp; ring
    have bq : ∀ v, |x v ^ 2 / (S v / S0)| ≤ ε₀ ^ 2 / (1 - ε₀) := fun v => by
      rw [abs_div, abs_of_pos (hrp v)]
      exact div_le_div₀ (sq_nonneg _) (bx2 v) hd (hr1 v)
    have iq : Integrable (fun v => x v ^ 2 / (S v / S0)) pm :=
      ibd pm ((mx.pow_const 2).div mr) bq
    have ix : Integrable x pm := ibd pm mx bx
    have e : ∫ v, (1 - 1 / (S v / S0)) ∂pm = -∫ v, x v ^ 2 / (S v / S0) ∂pm := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub ix iq]
      have : ∫ v, x v ∂pm = 0 := hmS
      rw [this]; ring
    rw [e, neg_sq]
    have h0 : 0 ≤ ∫ v, x v ^ 2 / (S v / S0) ∂pm :=
      integral_nonneg fun v => div_nonneg (sq_nonneg _) (hrp v).le
    have h1 : ∫ v, x v ^ 2 / (S v / S0) ∂pm ≤ (∫ v, x v ^ 2 ∂pm) / (1 - ε₀) := by
      rw [← integral_div]
      refine integral_mono iq (iX.div_const _) fun v => ?_
      exact div_le_div_of_nonneg_left (sq_nonneg _) hd (hr1 v)
    have := pow_le_pow_left₀ h0 h1 2
    rw [div_pow] at this
    exact this
  · -- the coefficient of `⟨u, z⟩`
    have hpt : ∀ v, (l v - l0) / (S v / S0) = δ v - δ v * (x v / (S v / S0)) := fun v => by
      rw [er v]
      have : (1 + x v) ≠ 0 := by rw [← er v]; exact (hrp v).ne'
      simp only [hδ]
      field_simp; ring
    have bq : ∀ v, |x v / (S v / S0)| ≤ ε₀ / (1 - ε₀) := fun v => by
      rw [abs_div, abs_of_pos (hrp v)]
      exact div_le_div₀ hε0 (bx v) hd (hr1 v)
    have mq : Measurable (fun v => x v / (S v / S0)) := mx.div mr
    have iq : Integrable (fun v => x v / (S v / S0)) pm := ibd pm mq bq
    have iδ : Integrable δ pm := ibd pm mδ bδ
    have iδq : Integrable (fun v => δ v * (x v / (S v / S0))) pm :=
      ibd pm (mδ.mul mq) (M := δ₀ * (ε₀ / (1 - ε₀))) fun v => by
        rw [abs_mul]; exact mul_le_mul (bδ v) (bq v) (abs_nonneg _) hδ0
    have e : ∫ v, (l v - l0) / (S v / S0) ∂pm = -∫ v, δ v * (x v / (S v / S0)) ∂pm := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub iδ iδq]
      have : ∫ v, δ v ∂pm = 0 := hml
      rw [this]; ring
    rw [e, neg_sq]
    have iδ2 : Integrable (fun v => δ v ^ 2) pm := ibd pm (mδ.pow_const 2) (M := δ₀ ^ 2) fun v => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bδ v) 2
    have iq2 : Integrable (fun v => (x v / (S v / S0)) ^ 2) pm :=
      ibd pm (mq.pow_const 2) (M := (ε₀ / (1 - ε₀)) ^ 2) fun v => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bq v) 2
    have hcs := BstLean.Part138.cs_sq pm iδ2 iq2 iδq
    have hq2 : ∫ v, (x v / (S v / S0)) ^ 2 ∂pm ≤ (∫ v, x v ^ 2 ∂pm) / (1 - ε₀) ^ 2 := by
      rw [← integral_div]
      refine integral_mono iq2 (iX.div_const _) fun v => ?_
      rw [div_pow]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (pow_le_pow_left₀ hd.le (hr1 v) 2)
    have hY : ∫ v, a2 * δ v ^ 2 ∂pm = a2 * ∫ v, δ v ^ 2 ∂pm := integral_const_mul _ _
    rw [hY]
    have hδ2 : 0 ≤ ∫ v, δ v ^ 2 ∂pm := integral_nonneg fun v => sq_nonneg _
    calc a2 * (∫ v, δ v * (x v / (S v / S0)) ∂pm) ^ 2
        ≤ a2 * ((∫ v, δ v ^ 2 ∂pm) * ∫ v, (x v / (S v / S0)) ^ 2 ∂pm) :=
          mul_le_mul_of_nonneg_left hcs ha2
      _ ≤ a2 * ((∫ v, δ v ^ 2 ∂pm) * ((∫ v, x v ^ 2 ∂pm) / (1 - ε₀) ^ 2)) := by gcongr
      _ = _ := by ring


end BstLean.Part207
