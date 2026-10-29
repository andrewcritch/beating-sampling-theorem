import BstLean.Part168XK
import BstLean.Part212Polar

/-! The exact order-160 polar bound applies to the actual admissible plane coefficients. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part160 BstLean.Part157
open BstLean.Part150 (hT sT rhoC binMean)
open BstLean.Part167 BstLean.Part168
variable {n : ℕ}

noncomputable def Xint160 (c : Fin n → ℝ) (τ : ℝ) (x u w : Fin n → ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (ξ₁ ξ₂ : Fin (mA n) → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (latSq (vecMul (planeP (2 / ((mA n : ℕ) : ℝ)) (reluV (A₁ *ᵥ x))
      (hT n A₁ c τ) (gate (Yf A₁)) ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 80)

lemma alg80 (A D M g t l : ℝ) :
    A / D * (g * t * l) ^ 80 * M = A / D * M * (g * t) ^ 80 * l ^ 80 := by ring

variable {u w : Fin n → ℝ} {s cs : ℝ}

theorem inner_frame160 (hn : 4 ≤ n) {q : ℕ} (hq : 1 ≤ q) (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (hsc : s ^ 2 + cs ^ 2 = 1) {c : Fin n → ℝ} {r : ℝ}
    (hcu : c = r • u) (τ : ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hY1 : ∀ A p, normSq (Yf A p) ≤ 1)
    (hYadm : ∀ A A', sT n A c τ = sT n A' c τ → Yf A = Yf A') (ξ₁ ξ₂ : Fin (mA n) → ℝ) :
    ∫⁻ A₁, Xint160 c τ (s • u + cs • w) u w Yf A₁ ξ₁ ξ₂ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal (radialProduct (n - 1 - 1) 80 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 80 *
        ((((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / q) * (((n - 1 - 1 : ℕ) : ℝ) + 160 * q) ^ 80)) *
        (2 / (n : ℝ) * (2 / ((mA n : ℕ) : ℝ))) ^ 80 * lamP ξ₁ ξ₂ ^ 80) := by
  have hn2 : 2 ≤ n := by omega
  have hd : 2 ≤ n - 1 - 1 := by omega
  have hm0 : 0 < mA n := by unfold mA; have : 0 < n := by omega
                            positivity
  rw [gaussMat_frame hn2 (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs)]
  refine (lintegral_map_le _ (measurable_Aframe _ _ _).aemeasurable).trans ?_
  have hrw : ∀ W, Xint160 c τ (s • u + cs • w) u w Yf
      (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W) ξ₁ ξ₂ =
      ENNReal.ofReal (normSq (∑ i, kap hn2 c τ u w s cs Yf ξ₁ ξ₂ W i • (W i).2.2) ^ 80) := by
    intro W
    unfold Xint160
    rw [latSq_vecMul_frame hn2 hu hw huw hsc (2 / (n : ℝ)) W]
    simp only [kap]
  rw [lintegral_congr hrw]
  have hB0 : 0 ≤ 2 / (n : ℝ) * (2 / ((mA n : ℕ) : ℝ)) * lamP ξ₁ ξ₂ := by
    have := lamP_nonneg ξ₁ ξ₂; positivity
  have hP := polar_core160 hm0 hd hq (kap hn2 c τ u w s cs Yf ξ₁ ξ₂)
    (kap_inv hn2 hu hw huw hsc hcu τ Yf hYadm ξ₁ ξ₂) hB0 (kap_le hn2 c τ Yf hY1 ξ₁ ξ₂)
  exact hP.trans (le_of_eq (congrArg ENNReal.ofReal (alg80 _ _ _ _ _ _)))

/-- Both actual network directions satisfy the plane coefficient premises. -/
theorem inner_frame_fields160 (hn : 4 ≤ n) {q : ℕ} (hq : 1 ≤ q)
    (hu : normSq u = 1) (hw : normSq w = 1) (huw : ∑ i, u i * w i = 0)
    (hsc : s ^ 2 + cs ^ 2 = 1) {c : Fin n → ℝ} {r : ℝ} (hcu : c = r • u)
    (τ : ℝ) (ξ₁ ξ₂ : Fin (mA n) → ℝ) :
    let B := ENNReal.ofReal (radialProduct (n - 1 - 1) 80 /
      (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 80 *
      ((mA n : ℝ) ^ ((1 : ℝ) / q) * (((n - 1 - 1 : ℕ) : ℝ) + 160 * q) ^ 80) *
      (2 / (n : ℝ) * (2 / (mA n : ℝ))) ^ 80 * lamP ξ₁ ξ₂ ^ 80)
    (∫⁻ A₁, Xint160 c τ (s • u + cs • w) u w (fun A => YF A c τ) A₁ ξ₁ ξ₂
      ∂gaussMat (mA n) n (2 / (n : ℝ))) ≤ B ∧
    (∫⁻ A₁, Xint160 c τ (s • u + cs • w) u w (fun A => YS A c τ) A₁ ξ₁ ξ₂
      ∂gaussMat (mA n) n (2 / (n : ℝ))) ≤ B := by
  constructor
  · exact inner_frame160 hn hq hu hw huw hsc hcu τ (fun A => YF A c τ)
      (fun A p => BstLean.Part167.normSq_bhat_le _) (fun A A' h => YF_adm c τ h) ξ₁ ξ₂
  · exact inner_frame160 hn hq hu hw huw hsc hcu τ (fun A => YS A c τ)
      (fun A p => BstLean.Part167.normSq_bhat_le _) (fun A A' h => YS_adm c τ h) ξ₁ ξ₂
end BstLean.Part212
