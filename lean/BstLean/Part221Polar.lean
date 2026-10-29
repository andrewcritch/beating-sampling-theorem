import BstLean.Part212Polar
import BstLean.Part217Direction

/-! The active maximum applies to coefficients that depend on all retained data. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_smul)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part168 (rows_pol_le ae_all_ne normSq_eq_radF)
open BstLean.Part217

noncomputable def coordinateGate (z : ℝ) : Bool := if 0 < z then true else false

noncomputable def activeRadius {m d : ℕ} (hm : 0 < m)
    (Z : Fin m → ℝ) (G : Fin m → Fin d → ℝ) : ℝ :=
  activeMaximum hm (fun i => coordinateGate (Z i)) (fun i => radF53 (G i))

/-- The moment premise uses the same retained gate and radius distribution. -/
theorem polar_active160 {m d : ℕ} (hm : 0 < m) (hd : 2 ≤ d)
    (κ : (Fin m → ℝ × ℝ × (Fin d → ℝ)) → Fin m → ℝ)
    (hκ : ∀ W W' : Fin m → ℝ × ℝ × (Fin d → ℝ), (∀ i, (W i).1 = (W' i).1 ∧
      (W i).2.1 = (W' i).2.1 ∧ normSq (W i).2.2 = normSq (W' i).2.2) → κ W = κ W')
    (hoff : ∀ W i, (W i).1 ≤ 0 → κ W i = 0)
    {B M : ℝ} (hB0 : 0 ≤ B) (hB : ∀ W, normSq (κ W) ≤ B)
    (hM : (∫⁻ Z, ∫⁻ G, ENNReal.ofReal (activeRadius hm Z G ^ 160)
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))
      ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)) ≤ ENNReal.ofReal M) :
    (∫⁻ W, ENNReal.ofReal (normSq (∑ i, κ W i • (W i).2.2) ^ 80)
      ∂Measure.pi (fun _ : Fin m =>
        (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin d))))) ≤
      ENNReal.ofReal (BstLean.Part212.exactRadius d 80 ^ 160 * B ^ 80 * M) := by
  refine (rows_pol_le _).trans ?_
  let K := BstLean.Part212.exactRadius d 80 ^ 160 * B ^ 80
  have hK : 0 ≤ K := mul_nonneg (by positivity) (pow_nonneg hB0 _)
  have hin : ∀ (Z T : Fin m → ℝ) (G' : Fin m → Fin d → ℝ),
      (∫⁻ G, ENNReal.ofReal (normSq (∑ i,
        κ (fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i))) i •
          (radF53 (G' i) • unitF53 (G i))) ^ 80)
        ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))) ≤
      ENNReal.ofReal K * ENNReal.ofReal (activeRadius hm Z G' ^ 160) := by
    intro Z T G'
    let e : Fin d → ℝ := unitF53 (fun _ => 1)
    have hne : (fun _ : Fin d => (1 : ℝ)) ≠ 0 := by
      intro h; have := congrFun h ⟨0, by omega⟩; simp at this
    have hen : normSq e = 1 := by
      rw [normSq_eq_radF, BstLean.Part162.radF_unitF hne]; norm_num
    let W0 : Fin m → ℝ × ℝ × (Fin d → ℝ) := fun i => (Z i, T i, radF53 (G' i) • e)
    let c := κ W0
    have hae : ∀ᵐ G ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)),
        κ (fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i))) = c := by
      filter_upwards [ae_all_ne (m := m) (by omega : 1 ≤ d)] with G hG
      apply hκ
      intro i
      refine ⟨rfl, rfl, ?_⟩
      change normSq (radF53 (G' i) • unitF53 (G i)) = normSq (radF53 (G' i) • e)
      rw [normSq_smul, normSq_smul, hen, normSq_eq_radF, BstLean.Part162.radF_unitF (hG i)]
      ring
    have heq : (∫⁻ G, ENNReal.ofReal (normSq (∑ i,
        κ (fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i))) i •
          (radF53 (G' i) • unitF53 (G i))) ^ 80)
        ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))) =
      ∫⁻ G, ENNReal.ofReal (radF53 (∑ i, (c i * radF53 (G' i)) • unitF53 (G i)) ^ 160)
        ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) := by
      apply lintegral_congr_ae
      filter_upwards [hae] with G hG
      rw [hG]
      simp only [smul_smul, normSq_eq_radF, ← pow_mul]
    rw [heq]
    have hcoff : ∀ i, coordinateGate (Z i) = false → c i = 0 := by
      intro i hi
      apply hoff W0 i
      change Z i ≤ 0
      by_contra hn
      simp [coordinateGate, lt_of_not_ge hn] at hi
    have h := active_direction_lintegral hm hd (by norm_num : 1 ≤ 80)
      (fun i => coordinateGate (Z i)) (R := fun i => radF53 (G' i))
      (fun i => sqrt_nonneg _) hcoff (hB W0)
    refine h.trans_eq ?_
    rw [← ENNReal.ofReal_mul hK]
    apply congrArg ENNReal.ofReal
    change BstLean.Part212.exactRadius d 80 ^ 160 * (activeRadius hm Z G' ^ 2 * B) ^ 80 =
      (BstLean.Part212.exactRadius d 80 ^ 160 * B ^ 80) * activeRadius hm Z G' ^ 160
    rw [mul_pow, ← pow_mul]
    ring
  calc _ ≤ ∫⁻ Z, ∫⁻ T, ∫⁻ G', ENNReal.ofReal K * ENNReal.ofReal (activeRadius hm Z G' ^ 160)
        ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))
        ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)
        ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1) :=
      lintegral_mono fun Z => lintegral_mono fun T => lintegral_mono fun G' => hin Z T G'
    _ = ENNReal.ofReal K * (∫⁻ Z, ∫⁻ G', ENNReal.ofReal (activeRadius hm Z G' ^ 160)
        ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))
        ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)) := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal M := mul_le_mul' le_rfl hM
    _ = _ := by rw [← ENNReal.ofReal_mul hK]

end BstLean.Part221
