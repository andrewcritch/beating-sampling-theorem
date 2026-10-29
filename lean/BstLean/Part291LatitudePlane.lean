import BstLean.Part212PlaneSupply
import BstLean.Part291LatitudeInner

/-! Plane moment assembly with an explicit maximum-row moment and scalar enclosure. -/
namespace BstLean.BlueprintLow
open BstLean.Part212
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

theorem plane_frame_moment160_bound (hn : 4 ≤ n) (hm : (16000 : ℝ) ≤ ((mA n : ℕ) : ℝ)) {R X2 : ℝ} (hR : 0 ≤ R)
    (hmax : ∀ hm : 0 < mA n,
      (∫⁻ G, ENNReal.ofReal (Mx hm G ^ 160)
        ∂Measure.pi (fun _ : Fin (mA n) => stdGauss (Fin (n - 1 - 1)))) ≤
        ENNReal.ofReal R)
    (hscalar : radialProduct (n - 1 - 1) 80 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 80 *
      R * (2 / (n : ℝ) * (2 / (mA n : ℝ))) ^ 80 * planeEnvelope80 (mA n) ^ 80 ≤ X2 ^ 80)
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
      ENNReal.ofReal (X2 ^ 80) := by
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
      R *
      (2 / (n : ℝ) * (2 / ((mA n : ℕ) : ℝ))) ^ 80 with hKd
  have hdR : (2 : ℝ) ≤ ((n - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
  have hKd0 : 0 ≤ Kd := by
    rw [hKd]
    refine mul_nonneg (mul_nonneg ?_ ?_) (pow_nonneg (by positivity) _)
    · exact div_nonneg (radialProduct_pos (by omega : 1 ≤ n - 1 - 1) 80).le (pow_nonneg (by linarith) _)
    · exact hR
  have hin : ∀ ξ₁ ξ₂ : Fin (mA n) → ℝ,
      ∫⁻ A₁, Xint160 c τ x u w Yf A₁ ξ₁ ξ₂ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
        ENNReal.ofReal Kd * ENNReal.ofReal (lamP ξ₁ ξ₂ ^ 80) := by
    intro ξ₁ ξ₂
    rw [← ENNReal.ofReal_mul hKd0]
    exact inner_frame160_bound hn hmax hu hw huw hsc hcu τ Yf hY1 hYadm ξ₁ ξ₂
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
    _ ≤ ENNReal.ofReal (X2 ^ 80) := by
        rw [← ENNReal.ofReal_mul hKd0, hKd]
        exact ENNReal.ofReal_le_ofReal hscalar

theorem planeMoment_bound160_bound (hn : 4 ≤ n) (hm : (16000 : ℝ) ≤ ((mA n : ℕ) : ℝ)) {R X2 : ℝ} (hR : 0 ≤ R)
    (hmax : ∀ hm : 0 < mA n,
      (∫⁻ G, ENNReal.ofReal (Mx hm G ^ 160)
        ∂Measure.pi (fun _ : Fin (mA n) => stdGauss (Fin (n - 1 - 1)))) ≤
        ENNReal.ofReal R)
    (hscalar : radialProduct (n - 1 - 1) 80 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 80 *
      R * (2 / (n : ℝ) * (2 / (mA n : ℝ))) ^ 80 * planeEnvelope80 (mA n) ^ 80 ≤ X2 ^ 80)
    {c : Fin n → ℝ} (hc : c ≠ 0) (τ : ℝ) (a : Ix n) {v : Fin (n - 1) → ℝ} (hv : v ≠ 0)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hYm : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ ×
      ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) => Yf z.1 z.2))
    (hY1 : ∀ A p, normSq (Yf A p) ≤ 1)
    (hYadm : ∀ A A', sT n A c τ = sT n A' c τ → Yf A = Yf A') :
    planeMoment160 c τ a v Yf ≤ ENNReal.ofReal (X2 ^ 80) := by
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
  exact plane_frame_moment160_bound hn hm hR hmax hscalar hu hw huw hsc hcu τ Yf hYm hY1 hYadm


end BstLean.BlueprintLow
