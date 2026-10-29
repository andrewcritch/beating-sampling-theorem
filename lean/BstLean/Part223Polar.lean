import BstLean.Part168Pol
import BstLean.Part212Radius
import BstLean.Part223Maximum

/-! The order-256 polar coefficient estimate retains the exact radial product. -/
namespace BstLean.Part223
open BstLean.Part212
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_smul)
open BstLean.Part134
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF)
open BstLean.Part162 (radF_sq radF_nonneg radF_unitF radF_unitF_le
  dirsum_le_sqrt radF_sum_le integrable_radF_pow)
open BstLean.Part167 (Mx Mx_nonneg measurable_Mx)
open BstLean.Part168 (rows_pol_le ae_all_ne normSq_eq_radF)
variable {m d : ℕ}

theorem polar_core256 (hm : 0 < m) (hd : 2 ≤ d) {q : ℕ} (hq : 1 ≤ q)
    (κ : (Fin m → ℝ × ℝ × (Fin d → ℝ)) → Fin m → ℝ)
    (hκ : ∀ W W' : Fin m → ℝ × ℝ × (Fin d → ℝ), (∀ i, (W i).1 = (W' i).1 ∧
      (W i).2.1 = (W' i).2.1 ∧ normSq (W i).2.2 = normSq (W' i).2.2) → κ W = κ W')
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ W, normSq (κ W) ≤ B) :
    ∫⁻ W, ENNReal.ofReal (normSq (∑ i, κ W i • (W i).2.2) ^ 128) ∂Measure.pi (fun _ : Fin m =>
        (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin d)))) ≤
      ENNReal.ofReal (radialProduct d 128 / ((d : ℝ) - 1) ^ 128 * B ^ 128 *
        ((m : ℝ) ^ ((1 : ℝ) / q) * ((d : ℝ) + 256 * q) ^ 128)) := by
  have hd1 : 1 ≤ d := by omega
  have hNe : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set K : ℝ := radialProduct d 128 / ((d : ℝ) - 1) ^ 128 with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact div_nonneg (radialProduct_pos hd1 128).le (pow_nonneg (by linarith) _)
  refine (rows_pol_le _).trans ?_
  -- the inner bound
  have hin : ∀ (Z T : Fin m → ℝ) (G' : Fin m → Fin d → ℝ),
      ∫⁻ G, ENNReal.ofReal (normSq (∑ i, κ (fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i))) i •
        ((fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i))) i).2.2) ^ 128)
        ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ≤
      ENNReal.ofReal (K * B ^ 128) * ENNReal.ofReal (Mx hm G' ^ 256) := by
    intro Z T G'
    set e : Fin d → ℝ := unitF53 (fun _ => (1 : ℝ)) with he
    have hne1 : (fun _ : Fin d => (1 : ℝ)) ≠ 0 := by
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp at this
    have hen : normSq e = 1 := by rw [normSq_eq_radF, he, radF_unitF hne1]; norm_num
    set W0 : Fin m → ℝ × ℝ × (Fin d → ℝ) := fun i => (Z i, T i, radF53 (G' i) • e)
    set κ0 := κ W0
    set c : Fin m → ℝ := fun i => κ0 i * radF53 (G' i) with hc
    have hae : ∀ᵐ G ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)),
        ENNReal.ofReal (normSq (∑ i, κ (fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i))) i •
          ((fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i))) i).2.2) ^ 128) =
        ENNReal.ofReal (radF53 (∑ i, c i • unitF53 (G i)) ^ 256) := by
      filter_upwards [ae_all_ne (m := m) hd1] with G hG
      have hk : κ (fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i))) = κ0 := by
        refine hκ _ _ fun i => ⟨rfl, rfl, ?_⟩
        simp only [W0]
        rw [normSq_smul, normSq_smul, hen, normSq_eq_radF (unitF53 (G i)), radF_unitF (hG i)]
        ring
      rw [hk]
      have hs : ∑ i, κ0 i • (radF53 (G' i) • unitF53 (G i)) = ∑ i, c i • unitF53 (G i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
      have e2 : normSq (∑ i, κ0 i • (radF53 (G' i) • unitF53 (G i))) ^ 128 =
          radF53 (∑ i, c i • unitF53 (G i)) ^ 256 := by
        rw [hs, normSq_eq_radF, ← pow_mul]
      exact congrArg ENNReal.ofReal e2
    rw [lintegral_congr_ae hae]
    -- integrability
    have hmeas : Measurable (fun G : Fin m → Fin d → ℝ => radF53 (∑ i, c i • unitF53 (G i)) ^ 256) :=
      (measurable_radF.comp (Finset.measurable_sum _ fun i _ =>
        (measurable_unitF.comp (measurable_pi_apply i)).const_smul (c i))).pow_const 256
    have hbd : ∀ G : Fin m → Fin d → ℝ, radF53 (∑ i, c i • unitF53 (G i)) ^ 256 ≤
        (∑ i, |c i|) ^ 256 := by
      intro G
      refine pow_le_pow_left₀ (radF_nonneg _) ((radF_sum_le c _).trans ?_) 256
      refine Finset.sum_le_sum fun i _ => ?_
      have := radF_unitF_le (G i)
      have := abs_nonneg (c i)
      nlinarith
    have hI : Integrable (fun G : Fin m → Fin d → ℝ => radF53 (∑ i, c i • unitF53 (G i)) ^ 256)
        (Measure.pi (fun _ : Fin m => stdGauss (Fin d))) := by
      refine (integrable_const ((∑ i, |c i|) ^ 256)).mono' hmeas.aestronglyMeasurable
        (ae_of_all _ fun G => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (radF_nonneg _) _)]
      exact hbd G
    rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun G => pow_nonneg (radF_nonneg _) _),
      ← ENNReal.ofReal_mul (mul_nonneg hK0 (pow_nonneg hB0 _))]
    refine ENNReal.ofReal_le_ofReal ((dirsum_le_sqrt (by omega) hd c (by norm_num)).trans ?_)
    -- constants
    have hsq : √((d : ℝ) - 1) ^ 256 = ((d : ℝ) - 1) ^ 128 := by
      rw [show (256 : ℕ) = 2 * 128 from rfl, pow_mul, Real.sq_sqrt (by linarith)]
    rw [hsq]
    have hR := (radius_even d 128).le
    have hcM : radF53 c ^ 2 ≤ Mx hm G' ^ 2 * B := by
      rw [radF_sq]
      have h1 : ∀ i, c i ^ 2 ≤ Mx hm G' ^ 2 * κ0 i ^ 2 := by
        intro i
        have hr : radF53 (G' i) ≤ Mx hm G' :=
          Finset.le_sup' (fun i => radF53 (G' i)) (Finset.mem_univ i)
        have hr0 := radF_nonneg (G' i)
        simp only [hc, mul_pow]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr0 hr 2) (sq_nonneg _)
      calc ∑ i, c i ^ 2 ≤ ∑ i, Mx hm G' ^ 2 * κ0 i ^ 2 := Finset.sum_le_sum fun i _ => h1 i
        _ = Mx hm G' ^ 2 * normSq κ0 := by rw [← Finset.mul_sum]; rfl
        _ ≤ Mx hm G' ^ 2 * B := mul_le_mul_of_nonneg_left (hB W0) (sq_nonneg _)
    have hc256 : radF53 c ^ 256 ≤ B ^ 128 * Mx hm G' ^ 256 := by
      have := pow_le_pow_left₀ (sq_nonneg _) hcM 128
      calc radF53 c ^ 256 = (radF53 c ^ 2) ^ 128 := by rw [← pow_mul]
        _ ≤ (Mx hm G' ^ 2 * B) ^ 128 := this
        _ = B ^ 128 * Mx hm G' ^ 256 := by rw [mul_pow, ← pow_mul]; ring
    have hd1R : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    calc (∫ g, radF53 g ^ 256 ∂stdGauss (Fin d)) / ((d : ℝ) - 1) ^ 128 * radF53 c ^ 256
        ≤ radialProduct d 128 / ((d : ℝ) - 1) ^ 128 * (B ^ 128 * Mx hm G' ^ 256) := by
          exact mul_le_mul (div_le_div_of_nonneg_right hR (pow_nonneg hd1R.le _)) hc256
            (pow_nonneg (radF_nonneg c) _) hK0
      _ = K * B ^ 128 * Mx hm G' ^ 256 := by rw [hK]; ring
  -- integrate out
  set Mm : ℝ := (m : ℝ) ^ ((1 : ℝ) / q) * ((d : ℝ) + 256 * q) ^ 128
  have hG' : ∫⁻ G', ENNReal.ofReal (K * B ^ 128) * ENNReal.ofReal (Mx hm G' ^ 256)
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ≤ ENNReal.ofReal (K * B ^ 128 * Mm) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ENNReal.ofReal_mul (mul_nonneg hK0 (pow_nonneg hB0 _))]
    exact mul_le_mul_right (max_moment256 hm hq) _
  calc _ ≤ ∫⁻ Z, ∫⁻ T, ENNReal.ofReal (K * B ^ 128 * Mm)
        ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)
        ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1) :=
        lintegral_mono fun Z => lintegral_mono fun T =>
          (lintegral_mono fun G' => hin Z T G').trans hG'
    _ = ENNReal.ofReal (K * B ^ 128 * Mm) := by simp
end BstLean.Part223
