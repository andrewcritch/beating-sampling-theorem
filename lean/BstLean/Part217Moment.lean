import BstLean.Part217Integral
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Shifted tail moments use one distribution and add no event charge. -/
namespace BstLean.Part217
open MeasureTheory Real Set
open scoped ENNReal

lemma shifted_power_exp {a v : ℝ} (ha : 0 < a) (hv : 0 ≤ v) (k : ℕ) :
    (a + v) ^ k ≤ a ^ k * exp ((k : ℝ) / a * v) := by
  have h : a + v ≤ a * exp (v / a) := by
    have h := mul_le_mul_of_nonneg_left (add_one_le_exp (v / a)) ha.le
    have he : a * (v / a + 1) = a + v := by field_simp; ring
    simpa [he] using h
  calc (a + v) ^ k ≤ (a * exp (v / a)) ^ k :=
        pow_le_pow_left₀ (by positivity) h k
    _ = a ^ k * exp ((k : ℝ) / a * v) := by
        rw [mul_pow, ← exp_nat_mul]
        congr 2
        ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem shifted_tail_moment {Z : Ω → ℝ} (hZ : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    {a t c : ℝ} (ha : 0 < a) {ell : ℕ} (hell : 1 ≤ ell)
    (htail : ∀ v : ℝ, 0 < v → μ.real {ω | v < Z ω} ≤ exp (-t * v - c * v ^ 2 / 2)) :
    (∫⁻ ω, ENNReal.ofReal ((a + Z ω) ^ ell) ∂μ) ≤
      ENNReal.ofReal (a ^ ell) + ENNReal.ofReal ((ell : ℝ) * a ^ (ell - 1)) *
        shiftedIntegral c (((ell - 1 : ℕ) : ℝ) / a - t) := by
  obtain ⟨k, rfl⟩ : ∃ k, ell = k + 1 := ⟨ell - 1, by omega⟩
  let g : ℝ → ℝ := fun v => (k + 1 : ℝ) * (a + v) ^ k
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hg0 : ∀ᵐ v ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g v := by
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact ae_of_all _ fun v hv => by dsimp [g]; have : 0 < v := hv; positivity
  have key := lintegral_comp_eq_lintegral_meas_lt_mul μ (f := Z) (g := g)
    (ae_of_all _ hZ0) hZ.aemeasurable (fun v _ => hg.intervalIntegrable _ _) hg0
  have hint : ∀ v : ℝ, ∫ u in (0 : ℝ)..v, g u = (a + v) ^ (k + 1) - a ^ (k + 1) := by
    intro v
    dsimp [g]
    have hd : ∀ u : ℝ, HasDerivAt (fun x : ℝ => (a + x) ^ (k + 1))
        ((k + 1 : ℝ) * (a + u) ^ k) u := by
      intro u
      simpa using (((hasDerivAt_id u).const_add a).fun_pow (k + 1))
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hd u) (hg.intervalIntegrable 0 v)
  simp only [hint] at key
  have hdiff : ∀ ω, 0 ≤ (a + Z ω) ^ (k + 1) - a ^ (k + 1) := by
    intro ω
    exact sub_nonneg.mpr (pow_le_pow_left₀ ha.le (by linarith [hZ0 ω]) _)
  have hsplit : (∫⁻ ω, ENNReal.ofReal ((a + Z ω) ^ (k + 1)) ∂μ) =
      ENNReal.ofReal (a ^ (k + 1)) +
        ∫⁻ ω, ENNReal.ofReal ((a + Z ω) ^ (k + 1) - a ^ (k + 1)) ∂μ := by
    have he : ∀ ω, ENNReal.ofReal ((a + Z ω) ^ (k + 1)) =
        ENNReal.ofReal (a ^ (k + 1)) +
          ENNReal.ofReal ((a + Z ω) ^ (k + 1) - a ^ (k + 1)) := by
      intro ω
      rw [← ENNReal.ofReal_add (by positivity) (hdiff ω)]
      congr 1
      ring
    simp_rw [he]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  rw [hsplit, key]
  apply add_le_add_right
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hK0 : 0 ≤ (k + 1 : ℝ) * a ^ k := by positivity
  unfold shiftedIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  refine ae_of_all _ fun v hv => ?_
  rw [← ofReal_measureReal (μ := μ), ← ENNReal.ofReal_mul hK0]
  have hg1 : g v ≤ (k + 1 : ℝ) * a ^ k * exp ((k : ℝ) / a * v) := by
    dsimp [g]
    exact (mul_le_mul_of_nonneg_left (shifted_power_exp ha (le_of_lt hv) k)
      (by positivity)).trans_eq (by ring)
  have htail0 : 0 ≤ μ.real {ω | v < Z ω} := measureReal_nonneg
  have hgv0 : 0 ≤ g v := by dsimp [g]; have : 0 < v := hv; positivity
  rw [← ENNReal.ofReal_mul htail0]
  apply ENNReal.ofReal_le_ofReal
  calc μ.real {ω | v < Z ω} * g v ≤
      exp (-t * v - c * v ^ 2 / 2) *
        ((k + 1 : ℝ) * a ^ k * exp ((k : ℝ) / a * v)) :=
      mul_le_mul (htail v hv) hg1 hgv0 (exp_pos _).le
    _ = (k + 1 : ℝ) * a ^ k * exp (((k : ℝ) / a - t) * v - c * v ^ 2 / 2) := by
      calc _ = ((k + 1 : ℝ) * a ^ k) *
          (exp (-t * v - c * v ^ 2 / 2) * exp ((k : ℝ) / a * v)) := by ring
        _ = _ := by rw [← exp_add]; congr 2; ring

theorem shifted_tail_moment_bound {L : Ω → ℝ} (hL : Measurable L)
    (hL0 : ∀ ω, 0 ≤ L ω) {a t c J : ℝ} (ha : 0 < a) {ell : ℕ} (hell : 1 ≤ ell)
    (htail : ∀ v : ℝ, 0 < v → μ.real {ω | a + v < L ω} ≤
      exp (-t * v - c * v ^ 2 / 2)) (hJ0 : 0 ≤ J)
    (hJ : shiftedIntegral c (((ell - 1 : ℕ) : ℝ) / a - t) ≤ ENNReal.ofReal J) :
    Integrable (fun ω => L ω ^ ell) μ ∧
      (∫ ω, L ω ^ ell ∂μ) ≤ a ^ ell + (ell : ℝ) * a ^ (ell - 1) * J := by
  let Z : Ω → ℝ := fun ω => max (L ω - a) 0
  have hZ : Measurable Z := (hL.sub_const a).max measurable_const
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun _ => le_max_right _ _
  have hZtail : ∀ v : ℝ, 0 < v → μ.real {ω | v < Z ω} ≤
      exp (-t * v - c * v ^ 2 / 2) := by
    intro v hv
    have he : {ω | v < Z ω} = {ω | a + v < L ω} := by
      ext ω
      dsimp [Z]
      rw [lt_max_iff]
      constructor
      · rintro (h | h) <;> linarith
      · intro h; left; linarith
    rw [he]
    exact htail v hv
  have hb := shifted_tail_moment hZ hZ0 ha hell hZtail
  have hK : 0 ≤ (ell : ℝ) * a ^ (ell - 1) := by positivity
  have hpt : ∀ ω, ENNReal.ofReal (L ω ^ ell) ≤ ENNReal.ofReal ((a + Z ω) ^ ell) := by
    intro ω
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (hL0 ω)
    have := le_max_left (L ω - a) 0
    dsimp [Z]
    linarith
  have hfin : (∫⁻ ω, ENNReal.ofReal (L ω ^ ell) ∂μ) ≤
      ENNReal.ofReal (a ^ ell + (ell : ℝ) * a ^ (ell - 1) * J) := by
    refine (lintegral_mono hpt).trans (hb.trans ?_)
    calc ENNReal.ofReal (a ^ ell) + ENNReal.ofReal ((ell : ℝ) * a ^ (ell - 1)) *
          shiftedIntegral c (((ell - 1 : ℕ) : ℝ) / a - t) ≤
        ENNReal.ofReal (a ^ ell) + ENNReal.ofReal ((ell : ℝ) * a ^ (ell - 1)) *
          ENNReal.ofReal J := add_le_add_right (mul_le_mul' le_rfl hJ) _
      _ = _ := by rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_add
        (pow_nonneg ha.le _) (mul_nonneg hK hJ0)]
  have hi : Integrable (fun ω => L ω ^ ell) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hL.pow_const _).aestronglyMeasurable
      (ae_of_all _ fun ω => pow_nonneg (hL0 ω) _)).mp
      (ne_of_lt (hfin.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun ω => pow_nonneg (hL0 ω) _)] at hfin
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfin

end BstLean.Part217
