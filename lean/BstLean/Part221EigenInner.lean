import BstLean.Part221Inner
import BstLean.Part212Inner
import BstLean.Part221PlaneCoefficient

/-! The active radial bound applies to the actual Agent coefficient fields. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part160 BstLean.Part157
open BstLean.Part167 BstLean.Part168
open BstLean.Part212 (Xint160 exactRadius)

theorem inner_frame_eigen160 {n : ℕ} (hn : 4 ≤ n)
    {R2 : ℝ} (hR : ActiveRadialMoment160 n R2)
    {u w : Fin n → ℝ} {s cs : ℝ}
    (hu : normSq u = 1) (hw : normSq w = 1) (huw : ∑ i, u i * w i = 0)
    (hsc : s ^ 2 + cs ^ 2 = 1) {c : Fin n → ℝ} {r : ℝ}
    (hcu : c = r • u) (τ : ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ →
      (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hY1 : ∀ A p, normSq (Yf A p) ≤ 1)
    (hYadm : ∀ A A', BstLean.Part150.sT n A c τ = BstLean.Part150.sT n A' c τ → Yf A = Yf A')
    (ξ₁ ξ₂ : Fin (mA n) → ℝ) :
    (∫⁻ A₁, Xint160 c τ (s • u + cs • w) u w Yf A₁ ξ₁ ξ₂
      ∂gaussMat (mA n) n (2 / (n : ℝ))) ≤
      ENNReal.ofReal (exactRadius (n - 1 - 1) 80 ^ 160 * R2 ^ 80 *
        (2 / (n : ℝ) * (2 / (mA n : ℝ))) ^ 80 * planeEigen ξ₁ ξ₂ ^ 80) := by
  have hn2 : 2 ≤ n := by omega
  have hm : 0 < mA n := by
    unfold mA
    exact pow_pos (by omega : 0 < n) 2
  rw [gaussMat_frame hn2 (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs)]
  refine (lintegral_map_le _ (measurable_Aframe _ _ _).aemeasurable).trans ?_
  have hrw : ∀ W, Xint160 c τ (s • u + cs • w) u w Yf
      (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W) ξ₁ ξ₂ =
      ENNReal.ofReal (normSq (∑ i, kap hn2 c τ u w s cs Yf ξ₁ ξ₂ W i • (W i).2.2) ^ 80) := by
    intro W
    unfold Xint160
    rw [latSq_vecMul_frame hn2 hu hw huw hsc (2 / (n : ℝ)) W]
    rfl
  rw [lintegral_congr hrw]
  have hB0 : 0 ≤ 2 / (n : ℝ) * (2 / (mA n : ℝ)) * planeEigen ξ₁ ξ₂ := by
    have := planeEigen_nonneg ξ₁ ξ₂; positivity
  have hM := hR hm
  have h := polar_active160 hm (by omega) (kap hn2 c τ u w s cs Yf ξ₁ ξ₂)
    (kap_inv hn2 hu hw huw hsc hcu τ Yf hYadm ξ₁ ξ₂)
    (kap_off hn2 hu hw huw hsc c τ Yf ξ₁ ξ₂)
    hB0 (kap_eigen hn2 c τ Yf hY1 ξ₁ ξ₂) hM
  refine h.trans_eq ?_
  apply congrArg ENNReal.ofReal
  rw [mul_pow, mul_pow]
  ring

end BstLean.Part221
