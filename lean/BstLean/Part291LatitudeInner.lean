import BstLean.Part212Inner
import BstLean.Part291LatitudePolar

/-! The actual plane coefficients with the improved maximum-row input. -/
namespace BstLean.BlueprintLow
open BstLean.Part212
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part160 BstLean.Part157
open BstLean.Part150 (hT sT rhoC binMean)
open BstLean.Part167 BstLean.Part168
variable {n : ℕ}

variable {u w : Fin n → ℝ} {s cs : ℝ}

theorem inner_frame160_bound (hn : 4 ≤ n) {R : ℝ}
    (hmax : ∀ hm : 0 < mA n,
      (∫⁻ G, ENNReal.ofReal (Mx hm G ^ 160)
        ∂Measure.pi (fun _ : Fin (mA n) => stdGauss (Fin (n - 1 - 1)))) ≤
        ENNReal.ofReal R) (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (hsc : s ^ 2 + cs ^ 2 = 1) {c : Fin n → ℝ} {r : ℝ}
    (hcu : c = r • u) (τ : ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hY1 : ∀ A p, normSq (Yf A p) ≤ 1)
    (hYadm : ∀ A A', sT n A c τ = sT n A' c τ → Yf A = Yf A') (ξ₁ ξ₂ : Fin (mA n) → ℝ) :
    ∫⁻ A₁, Xint160 c τ (s • u + cs • w) u w Yf A₁ ξ₁ ξ₂ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal (radialProduct (n - 1 - 1) 80 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 80 *
        R *
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
  have hP := polar_core160_bound hm0 hd (hmax hm0) (kap hn2 c τ u w s cs Yf ξ₁ ξ₂)
    (kap_inv hn2 hu hw huw hsc hcu τ Yf hYadm ξ₁ ξ₂) hB0 (kap_le hn2 c τ Yf hY1 ξ₁ ξ₂)
  exact hP.trans (le_of_eq (congrArg ENNReal.ofReal (alg80 _ _ _ _ _ _)))


end BstLean.BlueprintLow
