import BstLean.Part162LS
import BstLean.Part160MFB1
import BstLean.Part107WickA

/-! A radial cutoff preserves the isotropic second-moment factor. -/
namespace BstLean.Part198
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part130
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF)
open BstLean.Part162 (polar_integral_mul unitF_smul radF_sq)
open BstLean.Part160.MFB

theorem gaussian_direction_second {n : ℕ} (hn : 1 ≤ n) (b : Fin n → ℝ) :
    ∫ z, (b ⬝ᵥ unitF53 z) ^ 2 ∂stdGauss (Fin n) = normSq b / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := polar_integral_mul (fun u : Fin n → ℝ => (b ⬝ᵥ u) ^ 2)
    (fun r => r ^ 2) (by unfold dotProduct; fun_prop) (by fun_prop)
  have he : ∀ z : Fin n → ℝ,
      (b ⬝ᵥ unitF53 z) ^ 2 * radF53 z ^ 2 = (z ⬝ᵥ b) ^ 2 := by
    intro z
    conv_rhs => rw [← unitF_smul z]
    rw [smul_dotProduct, smul_eq_mul, dotProduct_comm, mul_pow]
    ring
  simp_rw [he] at h
  rw [(lin_moments b).2.2.2.1] at h
  have hrad : ∫ z, radF53 z ^ 2 ∂stdGauss (Fin n) = n := by
    simp_rw [radF_sq]
    rw [BstLean.Part107.normSq_mom1]
    simp
  rw [hrad] at h
  apply (eq_div_iff hnR.ne').mpr
  exact h.symm

/-- The low-radius linear second moment pays the tail probability, without its square root. -/
theorem gaussian_radial_cutoff {n : ℕ} (hn : 1 ≤ n) (b : Fin n → ℝ)
    {S : ℝ} (hS0 : 0 ≤ S) :
    (∫ z in {z : Fin n → ℝ | normSq z < S}, (b ⬝ᵥ z) ^ 2 ∂stdGauss (Fin n)) ≤
      normSq b / n * S * (stdGauss (Fin n)).real {z | normSq z < S} := by
  classical
  let B : Set (Fin n → ℝ) := {z | normSq z < S}
  have hB : MeasurableSet B := measurableSet_lt continuous_normSq.measurable measurable_const
  let w : ℝ → ℝ := fun r => if r ^ 2 < S then r ^ 2 else 0
  have hw : Measurable w := Measurable.ite
    (measurableSet_lt (measurable_id.pow_const 2) measurable_const)
    (measurable_id.pow_const 2) measurable_const
  have hpolar := polar_integral_mul (fun u : Fin n → ℝ => (b ⬝ᵥ u) ^ 2)
    w (by unfold dotProduct; fun_prop) hw
  have he : ∀ z : Fin n → ℝ, (b ⬝ᵥ unitF53 z) ^ 2 * w (radF53 z) =
      B.indicator (fun z => (b ⬝ᵥ z) ^ 2) z := by
    intro z
    have hrad : radF53 z ^ 2 = normSq z := radF_sq z
    by_cases hz : z ∈ B
    · rw [indicator_of_mem hz]
      simp only [w, hrad, show normSq z < S from hz, if_pos]
      conv_rhs => rw [← unitF_smul z]
      rw [dotProduct_smul, smul_eq_mul, mul_pow, ← hrad]
      ring
    · rw [indicator_of_notMem hz]
      simp [w, hrad, show ¬normSq z < S from hz]
  simp_rw [he] at hpolar
  rw [integral_indicator hB, gaussian_direction_second hn b] at hpolar
  have hi : Integrable (fun z : Fin n → ℝ => w (radF53 z)) (stdGauss (Fin n)) := by
    apply (integrable_const S).mono' (hw.comp measurable_radF).aestronglyMeasurable
    filter_upwards [] with z
    dsimp [w]
    split_ifs with hz
    · rw [abs_of_nonneg (sq_nonneg _)]
      exact hz.le
    · simpa using hS0
  have hb : ∫ z, w (radF53 z) ∂stdGauss (Fin n) ≤
      S * (stdGauss (Fin n)).real B := by
    calc _ ≤ ∫ z, B.indicator (fun _ => S) z ∂stdGauss (Fin n) := by
          apply integral_mono hi ((integrable_const S).indicator hB)
          intro z
          have hrad : radF53 z ^ 2 = normSq z := radF_sq z
          by_cases hz : z ∈ B
          · rw [indicator_of_mem hz]
            simp only [w, hrad, show normSq z < S from hz, if_pos]
            exact hz.le
          · rw [indicator_of_notMem hz]
            simp [w, hrad, show ¬normSq z < S from hz]
      _ = _ := by rw [integral_indicator_const _ hB, smul_eq_mul]; ring
  rw [hpolar]
  have h := mul_le_mul_of_nonneg_left hb (div_nonneg (normSq_nonneg b) (Nat.cast_nonneg n))
  convert h using 1 <;> ring

/-- The chi-square cutoff gives a linear, rather than square-root, exponential charge. -/
theorem gaussian_radial_cutoff_LM {n : ℕ} (hn : 1 ≤ n) (b : Fin n → ℝ)
    {S : ℝ} (hS0 : 0 ≤ S) (hS : S ≤ (n : ℝ) - 2 * √((n : ℝ) * 12)) :
    (∫ z in {z : Fin n → ℝ | normSq z < S}, (b ⬝ᵥ z) ^ 2 ∂stdGauss (Fin n)) ≤
      normSq b * exp (-12) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hp : (stdGauss (Fin n)).real {z : Fin n → ℝ | normSq z < S} ≤ exp (-12) := by
    apply (measureReal_mono (show {z : Fin n → ℝ | normSq z < S} ⊆
      {z | ∑ i, z i ^ 2 ≤ (Fintype.card (Fin n) : ℝ) -
        2 * √((Fintype.card (Fin n) : ℝ) * 12)} from
      fun z hz => by simpa only [Fintype.card_fin, mem_setOf_eq, normSq] using hz.le.trans hS)).trans
      (BstLean.Part152.chiSq_lower_LM (by norm_num))
  have hs : S ≤ n := hS.trans (by linarith [sqrt_nonneg ((n : ℝ) * 12)])
  have hcoef : normSq b / n * S ≤ normSq b := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hnR).mpr (mul_le_mul_of_nonneg_left hs (normSq_nonneg b))
  exact (gaussian_radial_cutoff hn b hS0).trans
    (mul_le_mul hcoef hp (measureReal_nonneg) (normSq_nonneg b))

#print axioms gaussian_direction_second
#print axioms gaussian_radial_cutoff
#print axioms gaussian_radial_cutoff_LM

theorem row_radial_cutoff_LM {n : ℕ} (hn : 1 ≤ n) (b : Fin n → ℝ)
    {S : ℝ} (hS0 : 0 ≤ S) (hS : S ≤ (n : ℝ) - 2 * √((n : ℝ) * 12)) :
    (∫ a, (b ⬝ᵥ a) ^ 2 *
      ({a : Fin n → ℝ | normSq a < 2 / (n : ℝ) * S}).indicator (fun _ => (1 : ℝ)) a
        ∂BstLean.Part153.rowLaw n) ≤ exp (-12) * (2 / (n : ℝ) * normSq b) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : 0 < 2 / (n : ℝ) := by positivity
  have hm : Measurable (fun a : Fin n → ℝ => (b ⬝ᵥ a) ^ 2 *
      ({a : Fin n → ℝ | normSq a < 2 / (n : ℝ) * S}).indicator (fun _ => (1 : ℝ)) a) :=
    ((meas_dot'_L1c b).pow_const 2).mul (measurable_const.indicator
      (measurableSet_lt continuous_normSq.measurable measurable_const))
  rw [rl_int hm]
  have he : ∀ z : Fin n → ℝ,
      (b ⬝ᵥ (√(2 / (n : ℝ)) • z)) ^ 2 *
        ({a : Fin n → ℝ | normSq a < 2 / (n : ℝ) * S}).indicator (fun _ => (1 : ℝ))
          (√(2 / (n : ℝ)) • z) =
      (2 / (n : ℝ)) * ({z : Fin n → ℝ | normSq z < S}).indicator
        (fun z => (b ⬝ᵥ z) ^ 2) z := by
    intro z
    have heq : normSq (√(2 / (n : ℝ)) • z) < 2 / (n : ℝ) * S ↔ normSq z < S := by
      rw [normSq_smul, sq_sqrt hscale.le]
      constructor <;> intro h <;> nlinarith
    by_cases hz : normSq z < S
    · rw [indicator_of_mem (show (√(2 / (n : ℝ)) • z) ∈
        {a : Fin n → ℝ | normSq a < 2 / (n : ℝ) * S} from heq.mpr hz),
        indicator_of_mem (show z ∈ {z : Fin n → ℝ | normSq z < S} from hz),
        dotProduct_smul, smul_eq_mul, mul_pow, sq_sqrt hscale.le, mul_one]
    · rw [indicator_of_notMem (show (√(2 / (n : ℝ)) • z) ∉
        {a : Fin n → ℝ | normSq a < 2 / (n : ℝ) * S} from mt heq.mp hz),
        indicator_of_notMem (show z ∉ {z : Fin n → ℝ | normSq z < S} from hz),
        mul_zero, mul_zero]
  simp_rw [he]
  rw [integral_const_mul, integral_indicator
    (measurableSet_lt continuous_normSq.measurable measurable_const)]
  have h := mul_le_mul_of_nonneg_left (gaussian_radial_cutoff_LM hn b hS0 hS) hscale.le
  convert h using 1 <;> ring

#print axioms row_radial_cutoff_LM
end BstLean.Part198
