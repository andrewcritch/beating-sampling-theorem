import BstLean.Part212LG
import BstLean.Part212Retained

/-! The fresh event supplies the actual lambda and residual certificates. -/
namespace BstLean.Part212
open MeasureTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (Ix muI lamX sigX)
open BstLean.Part162 (psiA)
open BstLean.Part166 (certI psiK fK sK)

lemma key_integral {n : ℕ} (k : AgFam n)
    (Φ : AgFam n → (Fin n → ℝ) → ℝ)
    (hΦ : Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) =>
      psiK Φ z.1 z.2.1 z.2.2)) {T : ℝ} (hT : 0 ≤ T)
    (hcert : certI Φ k ≤ ENNReal.ofReal (T ^ 12)) :
    ∫ a, ∫ v, psiK Φ k a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ T ^ 12 := by
  exact BstLean.Part166.integral_le_of_lintegral (muI n) (stdGauss (Fin (n - 1)))
    (fun a v => psiK Φ k a v ^ 12)
    ((hΦ.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).pow_const 12)
    (fun a v => pow_nonneg (BstLean.Part166.psiK_nonneg _ _ _ _) _)
    (pow_nonneg hT 12) hcert

theorem fresh_lambda_certificate {n : ℕ} (hn : 1 ≤ n) (D : Design n)
    (hD : AgentCentre154 D) (c : Ret n) {C : ℝ} (hC : 0 ≤ C)
    (he : 0 < normSq (D.bA c.1 c.2.1.1) / n)
    (hk : agKey D c ∈ latitudeEvent n (ENNReal.ofReal C)) :
    ∫ a, ∫ v, psiA (lamX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (C / (normSq (D.bA c.1 c.2.1.1) / n)) ^ 12 := by
  have hf := (latitudeEvent_fields hk).1
  rw [← ENNReal.ofReal_pow hC] at hf
  have hi := key_integral (agKey D c) fK BstLean.Part166.measurable_psiK_f hC hf
  let e := normSq (D.bA c.1 c.2.1.1) / n
  have hp (a : Ix n) (v : Fin (n - 1) → ℝ) :
      psiA (lamX D c) D c a v ^ 12 = e⁻¹ ^ 12 * psiK fK (agKey D c) a v ^ 12 := by
    have h := BstLean.Part166.psiA_lam_eq hn D hD c a v
    change e * psiA (lamX D c) D c a v = _ at h
    rw [← h, mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ he.ne', one_pow, one_mul]
  simp_rw [hp, integral_const_mul]
  calc e⁻¹ ^ 12 * (∫ a, ∫ v, psiK fK (agKey D c) a v ^ 12
      ∂stdGauss (Fin (n - 1)) ∂muI n) ≤ e⁻¹ ^ 12 * C ^ 12 :=
        mul_le_mul_of_nonneg_left hi (pow_nonneg (inv_nonneg.mpr he.le) 12)
    _ = _ := by rw [← mul_pow]; congr 1; dsimp [e]; ring

theorem fresh_residual_certificate {n : ℕ} (hn : 1 ≤ n) (D : Design n)
    (hD : AgentCentre154 D) (c : Ret n) {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey D c ∈ latitudeEvent n (ENNReal.ofReal C)) :
    ∫ a, ∫ v, psiA (sigX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (2 * C / n) ^ 12 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < (n : ℝ) / 2 := by positivity
  have hs := (latitudeEvent_fields hk).2
  have hm : Measurable (fun z : Ix n × (Fin (n - 1) → ℝ) =>
      ((n : ℝ) / 2 * psiK sK (agKey D c) z.1 z.2) ^ 12) :=
    (((BstLean.Part166.measurable_psiK_s).comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).const_mul _).pow_const _
  have hcert : ∫⁻ a, ∫⁻ v, ENNReal.ofReal
      (((n : ℝ) / 2 * psiK sK (agKey D c) a v) ^ 12)
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤ ENNReal.ofReal (C ^ 12) := by
    simp_rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg ha.le 12)]
    simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simpa only [latitudeCertZ, certI, ENNReal.ofReal_pow ha.le,
      ← ENNReal.ofReal_pow hC] using hs
  have hi := BstLean.Part166.integral_le_of_lintegral (muI n) (stdGauss (Fin (n - 1)))
    (fun a v => ((n : ℝ) / 2 * psiK sK (agKey D c) a v) ^ 12) hm
    (fun a v => pow_nonneg (mul_nonneg ha.le (BstLean.Part166.psiK_nonneg _ _ _ _)) 12)
    (pow_nonneg hC 12) hcert
  simp_rw [mul_pow, integral_const_mul] at hi
  simp_rw [BstLean.Part166.psiA_sig_eq D hD c]
  apply (mul_le_mul_iff_right₀ (pow_pos ha 12)).mp
  refine hi.trans (le_of_eq ?_)
  rw [← mul_pow]
  congr 1
  field_simp

theorem fresh_LG_lambda {n : ℕ} (hn : 26 ≤ n) (D : Design n)
    (hD : AgentCentre154 D) (c : Ret n) {C : ℝ} (hC : 0 < C)
    (he : 0 < normSq (D.bA c.1 c.2.1.1) / n)
    (hk : agKey D c ∈ latitudeEvent n (ENNReal.ofReal (C / n)))
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lamX D c (BstLean.Part161.xLat c (BstLean.Part161.latC D c a)
      (BstLean.Part53.unitF53 v)) -
      ∫ w, lamX D c (BstLean.Part161.xLat c (BstLean.Part161.latC D c a)
        (BstLean.Part53.unitF53 w)) ∂stdGauss (Fin (n - 1))| ^ (2 * q)
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤
    (BstLean.Part195.rotationConstant q *
      √((C / (normSq (D.bA c.1 c.2.1.1) / n)) /
        ((n : ℝ) * ((n : ℝ) - 1 - 2 * q)))) ^ (2 * q) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc12 := fresh_lambda_certificate (by omega) D hD c (div_nonneg hC.le hn0.le) he hk
  have heq : (C / n / (normSq (D.bA c.1 c.2.1.1) / n)) =
      C / (normSq (D.bA c.1 c.2.1.1) / n) / n := by ring
  rw [heq] at hc12
  exact latitude_moment_all hn D c (BstLean.Part162.lipLam_nonneg D c)
    (BstLean.Part162.lamX_euLip D c)
    (fun t x ht => BstLean.Part162.lamX_hom D c t x ht)
    (div_pos hC he) hc12 hq hq12

theorem fresh_LG_variance_lambda {n : ℕ} (hn : 26 ≤ n) (D : Design n)
    (hD : AgentCentre154 D) (c : Ret n) {C : ℝ} (hC : 0 < C)
    (he : 0 < normSq (D.bA c.1 c.2.1.1) / n)
    (hk : agKey D c ∈ latitudeEvent n (ENNReal.ofReal (C / n))) :
    √(∫ a, (∫ v, (lamX D c (BstLean.Part161.xLat c (BstLean.Part161.latC D c a)
      (BstLean.Part53.unitF53 v)) -
      ∫ w, lamX D c (BstLean.Part161.xLat c (BstLean.Part161.latC D c a)
        (BstLean.Part53.unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n) ≤
    (C / (normSq (D.bA c.1 c.2.1.1) / n)) /
      ((n : ℝ) * ((n : ℝ) - 3)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc12 := fresh_lambda_certificate (by omega) D hD c (div_nonneg hC.le hn0.le) he hk
  have heq : (C / n / (normSq (D.bA c.1 c.2.1.1) / n)) =
      C / (normSq (D.bA c.1 c.2.1.1) / n) / n := by ring
  rw [heq] at hc12
  exact latitude_variance_norm (by omega) D c (BstLean.Part162.lipLam_nonneg D c)
    (BstLean.Part162.lamX_euLip D c)
    (fun t x ht => BstLean.Part162.lamX_hom D c t x ht)
    (div_pos hC he) hc12

theorem fresh_LG_residual {n : ℕ} (hn : 26 ≤ n) (D : Design n)
    (hD : AgentCentre154 D) (c : Ret n) {C : ℝ} (hC : 0 < C)
    (hk : agKey D c ∈ latitudeEvent n (ENNReal.ofReal (C / n)))
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sigX D c (BstLean.Part161.xLat c (BstLean.Part161.latC D c a)
      (BstLean.Part53.unitF53 v)) -
      ∫ w, sigX D c (BstLean.Part161.xLat c (BstLean.Part161.latC D c a)
        (BstLean.Part53.unitF53 w)) ∂stdGauss (Fin (n - 1))| ^ (2 * q)
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤
    (BstLean.Part195.rotationConstant q *
      √((2 * C / n) / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q)))) ^ (2 * q) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc12 := fresh_residual_certificate (by omega) D hD c (div_nonneg hC.le hn0.le) hk
  have heq : 2 * (C / n) / n = (2 * C / n) / n := by ring
  rw [heq] at hc12
  exact latitude_moment_all hn D c (BstLean.Part162.lipSig_nonneg D c)
    (BstLean.Part162.sigX_euLip D c)
    (fun t x ht => BstLean.Part162.sigX_hom D c t x ht)
    (by positivity) hc12 hq hq12

theorem fresh_LG_variance_residual {n : ℕ} (hn : 26 ≤ n) (D : Design n)
    (hD : AgentCentre154 D) (c : Ret n) {C : ℝ} (hC : 0 < C)
    (hk : agKey D c ∈ latitudeEvent n (ENNReal.ofReal (C / n))) :
    √(∫ a, (∫ v, (sigX D c (BstLean.Part161.xLat c (BstLean.Part161.latC D c a)
      (BstLean.Part53.unitF53 v)) -
      ∫ w, sigX D c (BstLean.Part161.xLat c (BstLean.Part161.latC D c a)
        (BstLean.Part53.unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n) ≤
    (2 * C / n) / ((n : ℝ) * ((n : ℝ) - 3)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc12 := fresh_residual_certificate (by omega) D hD c (div_nonneg hC.le hn0.le) hk
  have heq : 2 * (C / n) / n = (2 * C / n) / n := by ring
  rw [heq] at hc12
  exact latitude_variance_norm (by omega) D c (BstLean.Part162.lipSig_nonneg D c)
    (BstLean.Part162.sigX_euLip D c)
    (fun t x ht => BstLean.Part162.sigX_hom D c t x ht)
    (by positivity) hc12
end BstLean.Part212
