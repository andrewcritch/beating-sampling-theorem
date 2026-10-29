import BstLean.Part168XM

/-!
# Part 168 (file `XK`)

The coefficients `κ = √γ p ⊙ D` in the frame: invariance (`kap_inv`), the bound (`kap_le`), and
the inner bound for fixed plane coordinates (`inner_frame`, from `polar_core`).

No proof is left open; no `native_decide` or `axiom` is used.
-/

namespace BstLean.Part168

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

variable {n : ℕ}


lemma alg64 (a b R M e f g B : ℝ) (hr : R ^ 64 = M) :
    a ^ 64 / b ^ 64 * (M * e ^ 64) * (f * g) ^ 64 * B ^ 64 =
      (a / b * (R * e) * f * g * B) ^ 64 := by
  rw [← hr]; ring

lemma X2q_pow {q : ℕ} (hq : 1 ≤ q) :
    (((n - 1 - 1 : ℕ) : ℝ) + 128) ^ 64 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 64 *
      ((((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / q) * (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) ^ 64)) *
      (2 / (n : ℝ) * (2 / ((mA n : ℕ) : ℝ))) ^ 64 * BL (mA n) ^ 64 = X2q n q ^ 64 := by
  have hm0 : (0 : ℝ) ≤ ((mA n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : (((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * q))) ^ (64 : ℕ) =
      ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]
    congr 1
    push_cast
    field_simp
  unfold X2q
  exact alg64 _ _ _ _ _ _ _ _ hr

lemma alg2 (A D M g t l : ℝ) :
    A / D * (g * t * l) ^ 64 * M = A / D * M * (g * t) ^ 64 * l ^ 64 := by ring

section frame

variable {u w : Fin n → ℝ} {s cs : ℝ}

/-- The coefficients `κ_i(W) = √γ p_i(W) D_i(W)` in the frame. -/
noncomputable def kap (hn2 : 2 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (u w : Fin n → ℝ) (s cs : ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (ξ₁ ξ₂ : Fin (mA n) → ℝ) (W : Fin (mA n) → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ)) :
    Fin (mA n) → ℝ := fun i =>
  √(2 / (n : ℝ)) * planeP (2 / ((mA n : ℕ) : ℝ))
      (reluV (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W *ᵥ (s • u + cs • w)))
      (hT n (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W) c τ)
      (gate (Yf (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W))) ξ₁ ξ₂ i *
    mask ((Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W *ᵥ (s • u + cs • w)) i)

/-- **Invariance**: `κ(W)` depends on `W` only through `(z_i, t_i, |Γ_i|²)`. -/
theorem kap_inv (hn2 : 2 ≤ n) (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (hsc : s ^ 2 + cs ^ 2 = 1) {c : Fin n → ℝ} {r : ℝ}
    (hcu : c = r • u) (τ : ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hYadm : ∀ A A', sT n A c τ = sT n A' c τ → Yf A = Yf A') (ξ₁ ξ₂ : Fin (mA n) → ℝ)
    (W W' : Fin (mA n) → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ))
    (h : ∀ i, (W i).1 = (W' i).1 ∧ (W i).2.1 = (W' i).2.1 ∧
      normSq (W i).2.2 = normSq (W' i).2.2) :
    kap hn2 c τ u w s cs Yf ξ₁ ξ₂ W = kap hn2 c τ u w s cs Yf ξ₁ ξ₂ W' := by
  have hγ : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  set A := Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W with hA
  set A' := Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W' with hA'
  have fr := frame_reads (m := mA n) hn2 hu hw huw hsc hγ W
  have fr' := frame_reads (m := mA n) hn2 hu hw huw hsc hγ W'
  have hAx : A *ᵥ (s • u + cs • w) = A' *ᵥ (s • u + cs • w) := by
    funext i; rw [(fr i).1, (fr' i).1, (h i).1]
  have hAu : A *ᵥ u = A' *ᵥ u := by
    funext i; rw [(fr i).2.1, (fr' i).2.1, (h i).1, (h i).2.1]
  have hAc : A *ᵥ c = A' *ᵥ c := by
    rw [hcu, Matrix.mulVec_smul, Matrix.mulVec_smul, hAu]
  have hrow : ∀ i, ∑ j, A i j ^ 2 = ∑ j, A' i j ^ 2 := by
    intro i; rw [(fr i).2.2, (fr' i).2.2, (h i).1, (h i).2.1, (h i).2.2]
  obtain ⟨hTe, hsTe⟩ := hT_adm c τ hAc hrow
  have hYe := hYadm _ _ hsTe
  unfold kap
  rw [← hA, ← hA', hAx, hTe, hYe]

/-- The coefficient bound `|κ|² ≤ γ t_A λ⁺`. -/
theorem kap_le (hn2 : 2 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hY1 : ∀ A p, normSq (Yf A p) ≤ 1) (ξ₁ ξ₂ : Fin (mA n) → ℝ)
    (W : Fin (mA n) → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ)) :
    normSq (kap hn2 c τ u w s cs Yf ξ₁ ξ₂ W) ≤
      2 / (n : ℝ) * (2 / ((mA n : ℕ) : ℝ)) * lamP ξ₁ ξ₂ := by
  have hγ : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have htA : (0 : ℝ) < 2 / ((mA n : ℕ) : ℝ) := by
    have : 0 < mA n := by unfold mA; have : 0 < n := by omega
                          positivity
    have : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast this
    positivity
  refine (normSq_coef_le hγ _ _).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (normSq_planeP_le htA _ _ _ (hY1 _) ξ₁ ξ₂) hγ

/-- **The inner bound** for fixed plane coordinates. -/
theorem inner_frame (hn : 4 ≤ n) {q : ℕ} (hq : 1 ≤ q) (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (hsc : s ^ 2 + cs ^ 2 = 1) {c : Fin n → ℝ} {r : ℝ}
    (hcu : c = r • u) (τ : ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hY1 : ∀ A p, normSq (Yf A p) ≤ 1)
    (hYadm : ∀ A A', sT n A c τ = sT n A' c τ → Yf A = Yf A') (ξ₁ ξ₂ : Fin (mA n) → ℝ) :
    ∫⁻ A₁, Xint c τ (s • u + cs • w) u w Yf A₁ ξ₁ ξ₂ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal ((((n - 1 - 1 : ℕ) : ℝ) + 128) ^ 64 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 64 *
        ((((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / q) * (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) ^ 64)) *
        (2 / (n : ℝ) * (2 / ((mA n : ℕ) : ℝ))) ^ 64 * lamP ξ₁ ξ₂ ^ 64) := by
  have hn2 : 2 ≤ n := by omega
  have hd : 2 ≤ n - 1 - 1 := by omega
  have hm0 : 0 < mA n := by unfold mA; have : 0 < n := by omega
                            positivity
  rw [gaussMat_frame hn2 (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs)]
  refine (lintegral_map_le _ (measurable_Aframe _ _ _).aemeasurable).trans ?_
  have hrw : ∀ W, Xint c τ (s • u + cs • w) u w Yf
      (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W) ξ₁ ξ₂ =
      ENNReal.ofReal (normSq (∑ i, kap hn2 c τ u w s cs Yf ξ₁ ξ₂ W i • (W i).2.2) ^ 64) := by
    intro W
    unfold Xint
    rw [latSq_vecMul_frame hn2 hu hw huw hsc (2 / (n : ℝ)) W]
    simp only [kap]
  rw [lintegral_congr hrw]
  have hB0 : 0 ≤ 2 / (n : ℝ) * (2 / ((mA n : ℕ) : ℝ)) * lamP ξ₁ ξ₂ := by
    have := lamP_nonneg ξ₁ ξ₂; positivity
  have hP := polar_core hm0 hd hq (kap hn2 c τ u w s cs Yf ξ₁ ξ₂)
    (kap_inv hn2 hu hw huw hsc hcu τ Yf hYadm ξ₁ ξ₂) hB0 (kap_le hn2 c τ Yf hY1 ξ₁ ξ₂)
  exact hP.trans (le_of_eq (congrArg ENNReal.ofReal (alg2 _ _ _ _ _ _)))

end frame

end BstLean.Part168
