import BstLean.Part168Pol
import BstLean.Part168Num

/-!
# Part 168 (file `XM`)

Measurability of the integrand of `Xmom`, the coefficient bound `|p|² ≤ t_A λ⁺`, and the
admissibility of `YF`, `YS` (they read `A₁` only through `s̃`).

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


/-! ## Measurability -/

lemma continuous_relu' : Continuous relu := by unfold relu; fun_prop

lemma measurable_binRow {m : ℕ} (c : Fin n → ℝ) (τ : ℝ) (i : Fin m) {g : ℝ → ℝ}
    (hg : Measurable g) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ =>
      binMean n (fun z => g (BstLean.Part150.mRow A c i + BstLean.Part150.sRow A τ i * z))) := by
  have ha : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => BstLean.Part150.mRow A c i) := by
    have : Continuous (fun A : Matrix (Fin m) (Fin n) ℝ => BstLean.Part150.mRow A c i) := by
      unfold BstLean.Part150.mRow; simp only [Matrix.mulVec, dotProduct]; fun_prop
    exact this.measurable
  have hs : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => BstLean.Part150.sRow A τ i) := by
    have : Continuous (fun A : Matrix (Fin m) (Fin n) ℝ => BstLean.Part150.sRow A τ i) := by
      unfold BstLean.Part150.sRow; fun_prop
    exact this.measurable
  exact BstLean.Part150.measurable_binMean_affine n hg ha hs

lemma measurable_hT_A {m : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => hT n A c τ) := by
  unfold hT
  exact measurable_pi_iff.mpr fun i => measurable_binRow c τ i continuous_relu'.measurable

lemma measurable_sT_A {m : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => sT n A c τ) := by
  unfold sT BstLean.Part150.sT2 BstLean.Part150.gT
  have h1 : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => ∑ i, binMean n (fun z =>
      relu (BstLean.Part150.mRow A c i + BstLean.Part150.sRow A τ i * z) ^ 2)) :=
    Finset.measurable_sum _ fun i _ =>
      measurable_binRow c τ i (continuous_relu'.measurable.pow_const 2)
  have h2 : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => ∑ i, hT n A c τ i ^ 2) :=
    Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (measurable_hT_A c τ)).pow_const 2
  exact ((h1.const_mul _).sub (h2.const_mul _)).sqrt

/-- `YF` is jointly measurable in `(A₁, p)`. -/
lemma measurable_YF_joint (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) =>
      YF z.1 c τ z.2) := by
  unfold YF bCore
  have hS := measurable_sT_A (n := n) (m := mA n) c τ
  have h1 : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ ×
      ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) => sT n z.1 c τ) := hS.comp measurable_fst
  have h : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ ×
      ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) =>
      fun j => binMean n (fun t => relu (z.2.2 j + sT n z.1 c τ * t))) := by
    refine measurable_pi_iff.mpr fun j => ?_
    exact BstLean.Part150.measurable_binMean_affine n continuous_relu'.measurable
      ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)) h1
  exact measurable_bhat.comp (h.const_smul (1 / rhoC c τ))

lemma measurable_YS_joint (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) =>
      YS z.1 c τ z.2) := by
  unfold YS
  have hr0 : Continuous (fun v : Fin (mA n) → ℝ => reluV v) := by
    unfold reluV relu; fun_prop
  have hr : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ ×
      ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) => reluV z.2.1) :=
    hr0.measurable.comp (measurable_fst.comp measurable_snd)
  have hy := measurable_YF_joint (n := n) c τ
  have hs : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ ×
      ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) => ∑ j, reluV z.2.1 j * YF z.1 c τ z.2 j) :=
    Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp hr).mul ((measurable_pi_apply j).comp hy)
  exact measurable_bhat.comp (hr.sub (hs.smul hy))

section planeMeas

variable {Q : Type*} [MeasurableSpace Q] {M : ℕ}

lemma measurable_lam_param {H G : Q → Fin M → ℝ} (hH : Measurable H) (hG : Measurable G) :
    Measurable (fun q => lam (H q) (G q)) := by
  unfold lam
  exact (Finset.measurable_sum _ fun j _ =>
    ((measurable_pi_apply j).comp hG).mul ((measurable_pi_apply j).comp hH)).div
    (measurable_normSq.comp hH)

lemma measurable_res_param {H G : Q → Fin M → ℝ} (hH : Measurable H) (hG : Measurable G) :
    Measurable (fun q => res (H q) (G q)) := by
  unfold res
  exact hG.sub ((measurable_lam_param hH hG).smul hH)

lemma measurable_cOf_param (v : ℝ) {H Ξ : Q → Fin M → ℝ} (hH : Measurable H)
    (hΞ : Measurable Ξ) : Measurable (fun q => cOf v (H q) (Ξ q)) := by
  unfold cOf
  have : Measurable (fun q => √(normSq (H q))) := (measurable_normSq.comp hH).sqrt
  exact (measurable_const.mul this).smul hΞ

/-- `planeP` is measurable in its parameters. -/
lemma measurable_planeP_param (v : ℝ) {H G Ξ1 Ξ2 : Q → Fin M → ℝ} (hH : Measurable H)
    (hG : Measurable G) (h1 : Measurable Ξ1) (h2 : Measurable Ξ2)
    {Wf : Q → (Fin M → ℝ) × (Fin M → ℝ) → Fin M → ℝ}
    (hW : Measurable (fun z : Q × ((Fin M → ℝ) × (Fin M → ℝ)) => Wf z.1 z.2)) :
    Measurable (fun q => planeP v (H q) (G q) (Wf q) (Ξ1 q) (Ξ2 q)) := by
  unfold planeP
  have hc1 := measurable_cOf_param v hH h1
  have hr := measurable_res_param hH hG
  have hc2 := measurable_cOf_param v hr h2
  have hl := measurable_lam_param hH hG
  have hP : Measurable (fun q => (cOf v (H q) (Ξ1 q),
      lam (H q) (G q) • cOf v (H q) (Ξ1 q) + cOf v (res (H q) (G q)) (Ξ2 q))) :=
    hc1.prodMk ((hl.smul hc1).add hc2)
  have hWP : Measurable (fun q => Wf q (cOf v (H q) (Ξ1 q),
      lam (H q) (G q) • cOf v (H q) (Ξ1 q) + cOf v (res (H q) (G q)) (Ξ2 q))) :=
    hW.comp (measurable_id.prodMk hP)
  refine ((((measurable_normSq.comp hH).inv.mul (Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hWP).mul ((measurable_pi_apply i).comp hc1)))).smul hH).add ?_
  exact (((measurable_normSq.comp hr).inv.mul (Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hWP).mul ((measurable_pi_apply i).comp hc2)))).smul hr

end planeMeas

/-- The integrand of `Xmom`. -/
noncomputable def Xint (c : Fin n → ℝ) (τ : ℝ) (x u w : Fin n → ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (ξ₁ ξ₂ : Fin (mA n) → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (latSq (vecMul (planeP (2 / ((mA n : ℕ) : ℝ)) (reluV (A₁ *ᵥ x))
      (hT n A₁ c τ) (gate (Yf A₁)) ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 64)

lemma measurable_Xint (c : Fin n → ℝ) (τ : ℝ) (x u w : Fin n → ℝ)
    {Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ}
    (hYm : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ ×
      ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) => Yf z.1 z.2)) :
    Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) =>
      Xint c τ x u w Yf z.1 z.2.1 z.2.2) := by
  unfold Xint
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
      latSq (vecMul pD.1 pD.2) u w ^ 64) := by
    unfold latSq; simp only [vecMul, dotProduct]; fun_prop
  have hD : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) ×
      (Fin (mA n) → ℝ) => D1A1 z.1 x) := (measurable_D1A1 x).comp hA
  have h1 := hL.measurable.comp (hp.prodMk hD)
  have h2 := ENNReal.measurable_ofReal.comp h1
  exact h2

/-! ## Invariance and the bound on the coefficients -/

lemma planeP_zero {M : ℕ} (v : ℝ) (g : Fin M → ℝ) (Y : (Fin M → ℝ) × (Fin M → ℝ) → Fin M → ℝ)
    (ξ₁ ξ₂ : Fin M → ℝ) : planeP v 0 g (gate Y) ξ₁ ξ₂ = 0 := by
  have h0 : cOf v (0 : Fin M → ℝ) ξ₁ = 0 := by
    unfold cOf; simp [normSq]
  unfold planeP
  rw [h0]
  simp [gate, BstLean.Part151.mask]

/-- `|p|² ≤ t_A λ⁺` for the plane part with a direction of norm at most `1`. -/
lemma normSq_planeP_le {M : ℕ} {v : ℝ} (hv : 0 < v) (h g : Fin M → ℝ)
    (Y : (Fin M → ℝ) × (Fin M → ℝ) → Fin M → ℝ) (hY : ∀ p, normSq (Y p) ≤ 1)
    (ξ₁ ξ₂ : Fin M → ℝ) : normSq (planeP v h g (gate Y) ξ₁ ξ₂) ≤ v * lamP ξ₁ ξ₂ := by
  by_cases hh : h = 0
  · subst hh
    rw [planeP_zero]
    have : normSq (0 : Fin M → ℝ) = 0 := by simp [normSq]
    rw [this]
    exact mul_nonneg hv.le (lamP_nonneg _ _)
  · set y := Y (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂)
    have e : planeP v h g (gate Y) ξ₁ ξ₂ =
        ((normSq h)⁻¹ * ∑ i, (mask (cOf v h ξ₁ i) * y i) * cOf v h ξ₁ i) • h +
        ((normSq (res h g))⁻¹ * ∑ i, (mask (cOf v h ξ₁ i) * y i) * cOf v (res h g) ξ₂ i) •
          res h g := rfl
    rw [e]
    refine (plane_norm hv hh g y ξ₁ ξ₂).trans ?_
    have := hY (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂)
    have hl := lamP_nonneg ξ₁ ξ₂
    have : v * normSq y * lamP ξ₁ ξ₂ ≤ v * 1 * lamP ξ₁ ξ₂ := by gcongr
    linarith

/-- `|√γ p ⊙ D|² ≤ γ|p|²`. -/
lemma normSq_coef_le {M : ℕ} {γ : ℝ} (hγ : 0 ≤ γ) (p e : Fin M → ℝ) :
    normSq (fun i => √γ * p i * mask (e i)) ≤ γ * normSq p := by
  unfold normSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt hγ, BstLean.Part151.mask_sq]
  have h1 : mask (e i) ≤ 1 := mask_le_one _
  have h0 := BstLean.Part151.mask_nonneg (e i)
  nlinarith [sq_nonneg (p i), mul_nonneg hγ (sq_nonneg (p i))]


lemma YF_adm (c : Fin n → ℝ) (τ : ℝ) {A A' : Matrix (Fin (mA n)) (Fin n) ℝ}
    (h : sT n A c τ = sT n A' c τ) : (fun p => YF A c τ p) = (fun p => YF A' c τ p) := by
  funext p
  unfold YF bCore
  rw [h]

lemma YS_adm (c : Fin n → ℝ) (τ : ℝ) {A A' : Matrix (Fin (mA n)) (Fin n) ℝ}
    (h : sT n A c τ = sT n A' c τ) : (fun p => YS A c τ p) = (fun p => YS A' c τ p) := by
  funext p
  unfold YS
  have e : YF A c τ = YF A' c τ := funext fun p => congrFun (YF_adm c τ h) p
  rw [e]

lemma measurable_Aframe (γ : ℝ) (x : Fin n → ℝ) (e' : Fin (n - 1) → ℝ) {m : ℕ} :
    Measurable (Aframe (m := m) γ x e') := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Aframe, Matrix.of_apply]
  exact ((measurable_pi_apply j).comp ((measurable_Rmap x e').comp
    (measurable_pi_apply i))).const_mul _


end BstLean.Part168
