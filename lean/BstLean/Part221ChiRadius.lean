import BstLean.Part93Chi
import BstLean.Part217Rate
import BstLean.Part153Op

/-! The exact chi-radius Chernoff rate and its Laurent--Massart calibration. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153

noncomputable def chiRadiusRate (d a : ℝ) : ℝ :=
  (a ^ 2 - d - d * log (a ^ 2 / d)) / 2

theorem gaussian_radius_chernoff {d : ℕ} (hd : 1 ≤ d) {a : ℝ}
    (ha : 0 < a) (ha2 : (d : ℝ) < a ^ 2) :
    (stdGauss (Fin d)).real {g | a < nrm g} ≤ exp (-chiRadiusRate d a) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hx : 0 < a ^ 2 / d - 1 := by
    rw [sub_pos, lt_div_iff₀ hd0, one_mul]
    exact ha2
  have h := BstLean.Part93.chiUp93 (Fin d) (a ^ 2 / d - 1) hx
  simp only [Fintype.card_fin] at h
  have ht : (1 + (a ^ 2 / d - 1)) * d = a ^ 2 := by field_simp; ring
  have he : (d : ℝ) * (a ^ 2 / d - 1 - log (1 + (a ^ 2 / d - 1))) / 2 =
      chiRadiusRate d a := by
    unfold chiRadiusRate
    rw [show 1 + (a ^ 2 / d - 1) = a ^ 2 / d by ring]
    field_simp
    <;> ring
  rw [ht, he] at h
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (exp_pos _).le] at hr
  refine (measureReal_mono (μ := stdGauss (Fin d)) ?_).trans hr
  intro g hg
  change a < √(normSq g) at hg
  change a ^ 2 ≤ normSq g
  have hs := Real.sq_sqrt (normSq_nonneg g)
  nlinarith

theorem chiRadiusRate_shift {d a v : ℝ} (hd : 0 < d) (ha : 0 < a) (hv : 0 ≤ v) :
    (a - d / a) * v + v ^ 2 / 2 ≤ chiRadiusRate d (a + v) - chiRadiusRate d a := by
  have hav : 0 < a + v := by linarith
  have h := BstLean.Part217.radialRate_shift hd.le ha hv
  unfold chiRadiusRate
  rw [log_div (pow_ne_zero _ hav.ne') hd.ne', log_div (pow_ne_zero _ ha.ne') hd.ne',
    log_pow, log_pow]
  unfold BstLean.Part217.radialRate at h
  push_cast
  linarith only [h]

theorem chiRadiusRate_calibration {d x a : ℝ} (hd : 0 < d) (hx : 0 < x) (ha : 0 < a)
    (ha2 : d + 2 * √d * √x + 2 * x ≤ a ^ 2) : x ≤ chiRadiusRate d a := by
  let u := √x / √d
  have hu : 0 < u := div_pos (sqrt_pos.mpr hx) (sqrt_pos.mpr hd)
  have hu1 : d * u = √d * √x := by
    dsimp only [u]
    have hs : √d ≠ 0 := (sqrt_pos.mpr hd).ne'
    calc
      d * (√x / √d) = (√d) ^ 2 * (√x / √d) := by rw [sq_sqrt hd.le]
      _ = √d * √x := by field_simp
  have hu2 : d * u ^ 2 = x := by
    dsimp only [u]
    rw [div_pow, sq_sqrt hx.le, sq_sqrt hd.le]
    field_simp
  have hexp : 1 + 2 * u + 2 * u ^ 2 ≤ exp (2 * u) := by
    have h := quadratic_le_exp_of_nonneg (by positivity : 0 ≤ 2 * u)
    nlinarith only [h]
  have hlog : log (1 + 2 * u + 2 * u ^ 2) ≤ 2 * u :=
    (log_le_iff_le_exp (by positivity)).mpr hexp
  let b := √(d + 2 * √d * √x + 2 * x)
  have hb : 0 < b := by dsimp [b]; positivity
  have hb2 : b ^ 2 = d + 2 * √d * √x + 2 * x := Real.sq_sqrt (by positivity)
  have hbd : d < b ^ 2 := by
    rw [hb2]
    nlinarith [mul_nonneg (sqrt_nonneg d) (sqrt_nonneg x)]
  have hba : b ≤ a := le_of_sq_le_sq (hb2.le.trans ha2) ha.le
  have hrat : b ^ 2 / d = 1 + 2 * u + 2 * u ^ 2 := by
    apply (div_eq_iff hd.ne').mpr
    rw [hb2]
    nlinarith only [hu1, hu2]
  have hbase : x ≤ chiRadiusRate d b := by
    unfold chiRadiusRate
    rw [hrat, hb2]
    have hl := mul_le_mul_of_nonneg_left hlog hd.le
    nlinarith only [hl, hu1]
  have hs := chiRadiusRate_shift hd hb (sub_nonneg.mpr hba)
  rw [show b + (a - b) = a by ring] at hs
  have ht := BstLean.Part217.radial_slope_pos hb hbd
  have hpos := mul_nonneg ht.le (sub_nonneg.mpr hba)
  nlinarith [sq_nonneg (a-b)]

end BstLean.Part221
