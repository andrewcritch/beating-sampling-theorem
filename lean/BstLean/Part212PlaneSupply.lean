import BstLean.Part212Inner
import BstLean.Part212PlaneMoment
import BstLean.Part212Components

/-! The plane moment uses the exact radial coefficient at order 160. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part160 BstLean.Part157
open BstLean.Part150 (hT sT rhoC binMean)
open BstLean.Part151 (mask measurable_mask)
open BstLean.Part161 (Ix uHat xLat)
open BstLean.Part162 (dirW)
open BstLean.Part166 (winC bhat measurable_bhat)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part167

open BstLean.Part168
variable {n : ℕ}

lemma measurable_planeIntegrand160 (c : Fin n → ℝ) (τ : ℝ) (x u w : Fin n → ℝ)
    {Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ}
    (hYm : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ ×
      ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) => Yf z.1 z.2)) :
    Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) =>
      Xint160 c τ x u w Yf z.1 z.2.1 z.2.2) := by
  unfold Xint160
  have hA : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) ×
      (Fin (mA n) → ℝ) => z.1) := measurable_fst
  have hH : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) ×
      (Fin (mA n) → ℝ) => reluV (z.1 *ᵥ x)) := by
    have : Continuous (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => reluV (A *ᵥ x)) := by
      unfold reluV relu; simp only [mulVec, dotProduct]; fun_prop
    exact this.measurable.comp hA
  have hG : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) ×
      (Fin (mA n) → ℝ) => hT n z.1 c τ) := (measurable_hT_A (n := n) c τ).comp hA
  have hW : Measurable (fun z : (Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) ×
      (Fin (mA n) → ℝ)) × ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) => gate (Yf z.1.1) z.2) := by
    unfold gate
    refine measurable_pi_iff.mpr fun j => ?_
    refine (measurable_mask.comp ((measurable_pi_apply j).comp (measurable_fst.comp
      measurable_snd))).mul ((measurable_pi_apply j).comp ?_)
    exact hYm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hp := measurable_planeP_param (2 / ((mA n : ℕ) : ℝ)) hH hG
    (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
    (Wf := fun z => gate (Yf z.1)) hW
  have hL : Continuous (fun pD : (Fin (mA n) → ℝ) × Matrix (Fin (mA n)) (Fin n) ℝ =>
      latSq (vecMul pD.1 pD.2) u w ^ 80) := by
    unfold latSq; simp only [vecMul, dotProduct]; fun_prop
  have hD : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) ×
      (Fin (mA n) → ℝ) => D1A1 z.1 x) := (measurable_D1A1 x).comp hA
  have h1 := hL.measurable.comp (hp.prodMk hD)
  have h2 := ENNReal.measurable_ofReal.comp h1
  exact h2

/-- The square of the plane amplitude retains the exact radial product. -/
noncomputable def planeEnvelopeSquared160 (n q : ℕ) : ℝ :=
  exactRadius (n - 1 - 1) 80 ^ 2 *
    ((mA n : ℝ) ^ ((1 : ℝ) / (80 * q)) * ((n - 1 - 1 : ℕ) + (160 : ℝ) * q)) *
    (2 / (n : ℝ)) * (2 / (mA n : ℝ)) * planeEnvelope80 (mA n)

lemma planeEnvelope_power160 (hn : 4 ≤ n) {q : ℕ} (hq : 1 ≤ q) :
    radialProduct (n - 1 - 1) 80 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 80 *
      ((mA n : ℝ) ^ ((1 : ℝ) / q) * (((n - 1 - 1 : ℕ) : ℝ) + 160 * q) ^ 80) *
      (2 / (n : ℝ) * (2 / (mA n : ℝ))) ^ 80 * planeEnvelope80 (mA n) ^ 80 =
      planeEnvelopeSquared160 n q ^ 80 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hm0 : (0 : ℝ) ≤ mA n := Nat.cast_nonneg _
  have hR : (exactRadius (n - 1 - 1) 80 ^ 2) ^ 80 =
      radialProduct (n - 1 - 1) 80 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 80 := by
    rw [← pow_mul]
    exact exactRadius_pow (by omega) (by norm_num)
  have hM : ((mA n : ℝ) ^ ((1 : ℝ) / (80 * q))) ^ (80 : ℕ) =
      (mA n : ℝ) ^ ((1 : ℝ) / q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]
    congr 1
    push_cast
    field_simp
  unfold planeEnvelopeSquared160
  simp only [mul_pow]
  rw [hR, hM]
  ring

lemma planeEnvelopeSquared_pos160 (hn : 4 ≤ n) {q : ℕ} (hq : 1 ≤ q) :
    0 < planeEnvelopeSquared160 n q := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdR : (2 : ℝ) ≤ (n - 1 - 1 : ℕ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
  have hmR : (0 : ℝ) < mA n := by
    exact_mod_cast (show 0 < mA n by unfold mA; positivity)
  have hR : 0 < exactRadius (n - 1 - 1) 80 := by
    unfold exactRadius
    exact div_pos (Real.rpow_pos_of_pos (radialProduct_pos (by omega) 80) _)
      (Real.sqrt_pos.mpr (by linarith))
  have hB : 0 < planeEnvelope80 (mA n) := by unfold planeEnvelope80; positivity
  unfold planeEnvelopeSquared160
  positivity
theorem plane_frame_moment160 (hn : 4 ≤ n) (hm : (16000 : ℝ) ≤ ((mA n : ℕ) : ℝ)) {q : ℕ} (hq : 1 ≤ q)
    {u w : Fin n → ℝ} {s cs : ℝ} (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (hsc : s ^ 2 + cs ^ 2 = 1) {c : Fin n → ℝ} {r : ℝ}
    (hcu : c = r • u) (τ : ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hYm : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ ×
      ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) => Yf z.1 z.2))
    (hY1 : ∀ A p, normSq (Yf A p) ≤ 1)
    (hYadm : ∀ A A', sT n A c τ = sT n A' c τ → Yf A = Yf A') :
    ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, Xint160 c τ (s • u + cs • w) u w Yf A₁ ξ₁ ξ₂
      ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal (planeEnvelopeSquared160 n q ^ 80) := by
  set x := s • u + cs • w with hx
  have hmeas := measurable_planeIntegrand160 c τ x u w hYm
  -- Tonelli: the plane coordinates outside
  have h3 : Measurable (fun z : (Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ)) ×
      (Fin (mA n) → ℝ) => Xint160 c τ x u w Yf z.1.1 z.1.2 z.2) := by
    have hg : Measurable (fun z : (Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ)) ×
        (Fin (mA n) → ℝ) => (z.1.1, z.1.2, z.2)) :=
      (measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have h4 := hmeas.comp hg
    exact h4
  have hm1 : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) =>
      ∫⁻ ξ₂, Xint160 c τ x u w Yf z.1 z.2 ξ₂ ∂stdGauss (Fin (mA n))) := h3.lintegral_prod_right'
  rw [lintegral_lintegral_swap hm1.aemeasurable]
  have hsw : ∀ ξ₁ : Fin (mA n) → ℝ,
      ∫⁻ A₁, ∫⁻ ξ₂, Xint160 c τ x u w Yf A₁ ξ₁ ξ₂ ∂stdGauss (Fin (mA n))
        ∂gaussMat (mA n) n (2 / (n : ℝ)) =
      ∫⁻ ξ₂, ∫⁻ A₁, Xint160 c τ x u w Yf A₁ ξ₁ ξ₂ ∂gaussMat (mA n) n (2 / (n : ℝ))
        ∂stdGauss (Fin (mA n)) := by
    intro ξ₁
    have hg : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) =>
        (z.1, ξ₁, z.2)) := measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
    have hm2 := hmeas.comp hg
    exact lintegral_lintegral_swap hm2.aemeasurable
  rw [lintegral_congr hsw]
  set Kd : ℝ := radialProduct (n - 1 - 1) 80 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 80 *
      ((((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / q) * (((n - 1 - 1 : ℕ) : ℝ) + 160 * q) ^ 80)) *
      (2 / (n : ℝ) * (2 / ((mA n : ℕ) : ℝ))) ^ 80 with hKd
  have hdR : (2 : ℝ) ≤ ((n - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
  have hKd0 : 0 ≤ Kd := by
    rw [hKd]
    refine mul_nonneg (mul_nonneg ?_ ?_) (pow_nonneg (by positivity) _)
    · exact div_nonneg (radialProduct_pos (by omega : 1 ≤ n - 1 - 1) 80).le (pow_nonneg (by linarith) _)
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (by positivity) _)
  have hin : ∀ ξ₁ ξ₂ : Fin (mA n) → ℝ,
      ∫⁻ A₁, Xint160 c τ x u w Yf A₁ ξ₁ ξ₂ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
        ENNReal.ofReal Kd * ENNReal.ofReal (lamP ξ₁ ξ₂ ^ 80) := by
    intro ξ₁ ξ₂
    rw [← ENNReal.ofReal_mul hKd0]
    exact inner_frame160 hn hq hu hw huw hsc hcu τ Yf hY1 hYadm ξ₁ ξ₂
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ A₁, Xint160 c τ x u w Yf A₁ ξ₁ ξ₂
        ∂gaussMat (mA n) n (2 / (n : ℝ)) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal Kd * ENNReal.ofReal (lamP ξ₁ ξ₂ ^ 80)
        ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hin ξ₁ ξ₂
    _ = ENNReal.ofReal Kd * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (lamP ξ₁ ξ₂ ^ 80)
        ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal Kd * ENNReal.ofReal (planeEnvelope80 (mA n) ^ 80) :=
        mul_le_mul_right (plane_eigenmoment80 hm) _
    _ = ENNReal.ofReal (planeEnvelopeSquared160 n q ^ 80) := by
        rw [← ENNReal.ofReal_mul hKd0, hKd, planeEnvelope_power160 hn hq]

/-- **The plane moment `X_ℓ`** (`planeMoment160`, the remaining sub-lemma 5 of Lemma LJ). -/
theorem planeMoment_bound160 (hn : 4 ≤ n) (hm : (16000 : ℝ) ≤ ((mA n : ℕ) : ℝ)) {q : ℕ} (hq : 1 ≤ q)
    {c : Fin n → ℝ} (hc : c ≠ 0) (τ : ℝ) (a : Ix n) {v : Fin (n - 1) → ℝ} (hv : v ≠ 0)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hYm : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ ×
      ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) => Yf z.1 z.2))
    (hY1 : ∀ A p, normSq (Yf A p) ≤ 1)
    (hYadm : ∀ A A', sT n A c τ = sT n A' c τ → Yf A = Yf A') :
    planeMoment160 c τ a v Yf ≤ ENNReal.ofReal (planeEnvelopeSquared160 n q ^ 80) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hu, hw, huw⟩ := frame_orth hn1 hc hv
  have hs2 : latitude (n := n) (√(normSq c)) τ a ^ 2 ≤ 1 := BstLean.Part162.latitude_sq_le _ _ _
  have hsc : latitude (n := n) (√(normSq c)) τ a ^ 2 +
      √(1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ 2 = 1 := by
    rw [Real.sq_sqrt (by linarith)]; ring
  have hx := BstLean.Part161.xLat_eq hn1 (c := rc c) hc (latitude (n := n) (√(normSq c)) τ a)
    (unitF53 v)
  have hcu : c = √(normSq c) • uHat (rc c) := by
    have e : (rc c).1.2 = c := rfl
    have hc0 : √(normSq c) ≠ 0 := by
      intro h0
      have hu0 : uHat (rc c) = 0 := by
        unfold uHat; rw [e, h0, _root_.inv_zero, zero_smul]
      rw [hu0] at hu
      simp [normSq] at hu
    unfold uHat
    rw [e, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hX : planeMoment160 c τ a v Yf = ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂,
      Xint160 c τ (latitude (n := n) (√(normSq c)) τ a • uHat (rc c) +
        √(1 - latitude (n := n) (√(normSq c)) τ a ^ 2) • dirW (rc c) (unitF53 v))
        (uHat (rc c)) (dirW (rc c) (unitF53 v)) Yf A₁ ξ₁ ξ₂
      ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ∂gaussMat (mA n) n (2 / (n : ℝ)) := by
    unfold planeMoment160 Xint160
    rw [hx]
    rfl
  rw [hX]
  exact plane_frame_moment160 hn hm hq hu hw huw hsc hcu τ Yf hYm hY1 hYadm

theorem planeMoments_bound160 (hn : 8000 ≤ n) {q : ℕ} (hq : 1 ≤ q)
    {c : Fin n → ℝ} {τ : ℝ} (hwin : winC c τ) (a : Ix n)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    planeMoment160 c τ a v (fun A => YF A c τ) ≤
      ENNReal.ofReal (planeEnvelopeSquared160 n q ^ 80) ∧
    planeMoment160 c τ a v (fun A => YS A c τ) ≤
      ENNReal.ofReal (planeEnvelopeSquared160 n q ^ 80) := by
  have hm : (16000 : ℝ) ≤ (mA n : ℝ) := by
    exact_mod_cast (show 16000 ≤ mA n by
      unfold mA
      calc 16000 ≤ 8000 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2)
  have hc := window_c_ne (by omega) hwin
  constructor
  · exact planeMoment_bound160 (by omega) hm hq hc τ a hv _ (measurable_YF_joint c τ)
      (fun A p => normSq_bhat_le _) (fun A A' h => YF_adm c τ h)
  · exact planeMoment_bound160 (by omega) hm hq hc τ a hv _ (measurable_YS_joint c τ)
      (fun A p => normSq_bhat_le _) (fun A A' h => YS_adm c τ h)
end BstLean.Part212
