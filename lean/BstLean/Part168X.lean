import BstLean.Part168XK

/-!
# Part 168 (file `X`)

**The plane moment `X_ℓ`** (sub-lemma 5 of Lemma LJ): `Xframe_le`, `Xmom_le`, `X_hyp_proved`.
`X2q n q = ((d+128)/(d−1))·m^{1/(64q)}(d+128q)·γ_A·t_A·BL(m)`.

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



/-- **The plane moment in the frame variables.** -/
theorem Xframe_le (hn : 4 ≤ n) (hm : (12800 : ℝ) ≤ ((mA n : ℕ) : ℝ)) {q : ℕ} (hq : 1 ≤ q)
    {u w : Fin n → ℝ} {s cs : ℝ} (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (hsc : s ^ 2 + cs ^ 2 = 1) {c : Fin n → ℝ} {r : ℝ}
    (hcu : c = r • u) (τ : ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hYm : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ ×
      ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) => Yf z.1 z.2))
    (hY1 : ∀ A p, normSq (Yf A p) ≤ 1)
    (hYadm : ∀ A A', sT n A c τ = sT n A' c τ → Yf A = Yf A') :
    ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, Xint c τ (s • u + cs • w) u w Yf A₁ ξ₁ ξ₂
      ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal (X2q n q ^ 64) := by
  set x := s • u + cs • w with hx
  have hmeas := measurable_Xint c τ x u w hYm
  -- Tonelli: the plane coordinates outside
  have h3 : Measurable (fun z : (Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ)) ×
      (Fin (mA n) → ℝ) => Xint c τ x u w Yf z.1.1 z.1.2 z.2) := by
    have hg : Measurable (fun z : (Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ)) ×
        (Fin (mA n) → ℝ) => (z.1.1, z.1.2, z.2)) :=
      (measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have h4 := hmeas.comp hg
    exact h4
  have hm1 : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) =>
      ∫⁻ ξ₂, Xint c τ x u w Yf z.1 z.2 ξ₂ ∂stdGauss (Fin (mA n))) := h3.lintegral_prod_right'
  rw [lintegral_lintegral_swap hm1.aemeasurable]
  have hsw : ∀ ξ₁ : Fin (mA n) → ℝ,
      ∫⁻ A₁, ∫⁻ ξ₂, Xint c τ x u w Yf A₁ ξ₁ ξ₂ ∂stdGauss (Fin (mA n))
        ∂gaussMat (mA n) n (2 / (n : ℝ)) =
      ∫⁻ ξ₂, ∫⁻ A₁, Xint c τ x u w Yf A₁ ξ₁ ξ₂ ∂gaussMat (mA n) n (2 / (n : ℝ))
        ∂stdGauss (Fin (mA n)) := by
    intro ξ₁
    have hg : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) =>
        (z.1, ξ₁, z.2)) := measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
    have hm2 := hmeas.comp hg
    exact lintegral_lintegral_swap hm2.aemeasurable
  rw [lintegral_congr hsw]
  set Kd : ℝ := (((n - 1 - 1 : ℕ) : ℝ) + 128) ^ 64 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 64 *
      ((((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / q) * (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) ^ 64)) *
      (2 / (n : ℝ) * (2 / ((mA n : ℕ) : ℝ))) ^ 64 with hKd
  have hdR : (2 : ℝ) ≤ ((n - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
  have hKd0 : 0 ≤ Kd := by
    rw [hKd]
    refine mul_nonneg (mul_nonneg ?_ ?_) (pow_nonneg (by positivity) _)
    · apply div_nonneg <;> apply pow_nonneg <;> linarith
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (by positivity) _)
  have hin : ∀ ξ₁ ξ₂ : Fin (mA n) → ℝ,
      ∫⁻ A₁, Xint c τ x u w Yf A₁ ξ₁ ξ₂ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
        ENNReal.ofReal Kd * ENNReal.ofReal (lamP ξ₁ ξ₂ ^ 64) := by
    intro ξ₁ ξ₂
    rw [← ENNReal.ofReal_mul hKd0]
    exact inner_frame hn hq hu hw huw hsc hcu τ Yf hY1 hYadm ξ₁ ξ₂
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ A₁, Xint c τ x u w Yf A₁ ξ₁ ξ₂
        ∂gaussMat (mA n) n (2 / (n : ℝ)) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal Kd * ENNReal.ofReal (lamP ξ₁ ξ₂ ^ 64)
        ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hin ξ₁ ξ₂
    _ = ENNReal.ofReal Kd * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (lamP ξ₁ ξ₂ ^ 64)
        ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal Kd * ENNReal.ofReal (BL (mA n) ^ 64) :=
        mul_le_mul_right (mom_lamP hm) _
    _ = ENNReal.ofReal (X2q n q ^ 64) := by
        rw [← ENNReal.ofReal_mul hKd0, hKd, X2q_pow hq]

/-- **The plane moment `X_ℓ`** (`Xmom`, the remaining sub-lemma 5 of Lemma LJ). -/
theorem Xmom_le (hn : 4 ≤ n) (hm : (12800 : ℝ) ≤ ((mA n : ℕ) : ℝ)) {q : ℕ} (hq : 1 ≤ q)
    {c : Fin n → ℝ} (hc : c ≠ 0) (τ : ℝ) (a : Ix n) {v : Fin (n - 1) → ℝ} (hv : v ≠ 0)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hYm : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ ×
      ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) => Yf z.1 z.2))
    (hY1 : ∀ A p, normSq (Yf A p) ≤ 1)
    (hYadm : ∀ A A', sT n A c τ = sT n A' c τ → Yf A = Yf A') :
    Xmom c τ a v Yf ≤ ENNReal.ofReal (X2q n q ^ 64) := by
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
  have hX : Xmom c τ a v Yf = ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂,
      Xint c τ (latitude (n := n) (√(normSq c)) τ a • uHat (rc c) +
        √(1 - latitude (n := n) (√(normSq c)) τ a ^ 2) • dirW (rc c) (unitF53 v))
        (uHat (rc c)) (dirW (rc c) (unitF53 v)) Yf A₁ ξ₁ ξ₂
      ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ∂gaussMat (mA n) n (2 / (n : ℝ)) := by
    unfold Xmom Xint
    rw [hx]
    rfl
  rw [hX]
  exact Xframe_le hn hm hq hu hw huw hsc hcu τ Yf hYm hY1 hYadm

/-- **`X_hyp` is proved** (any `q ≥ 1`, every `n ≥ 114`). -/
theorem X_hyp_proved (hn : 114 ≤ n) {q : ℕ} (hq : 1 ≤ q) : X_hyp n (X2q n q) := by
  have hm : (12800 : ℝ) ≤ ((mA n : ℕ) : ℝ) := by
    have : 12800 ≤ mA n := by
      unfold mA
      calc 12800 ≤ 114 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
    exact_mod_cast this
  intro c τ hwin a v hv
  have hc := window_c_ne (by omega) hwin
  refine ⟨?_, ?_⟩
  · exact Xmom_le (by omega) hm hq hc τ a hv _ (measurable_YF_joint c τ)
      (fun A p => normSq_bhat_le _) (fun A A' h => YF_adm c τ h)
  · exact Xmom_le (by omega) hm hq hc τ a hv _ (measurable_YS_joint c τ)
      (fun A p => normSq_bhat_le _) (fun A A' h => YS_adm c τ h)


end BstLean.Part168
