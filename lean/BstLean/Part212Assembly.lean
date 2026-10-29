import BstLean.Part167Asm
import BstLean.Part212TransverseLatitude

/-! Assemble the plane, Frobenius and operator moments at order 160. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part160
open BstLean.Part157 (cOf)
open BstLean.Part152 (opN opN_nonneg)
open BstLean.Part153 (nrm nrm_nonneg nuA nrm_mulVec_le)
open BstLean.Part150 (hT)
open BstLean.Part151 (mask)
open BstLean.Part161 (Ix uHat xLat)
open BstLean.Part162 (dirW)
open BstLean.Part166 (winC bhat)
open BstLean.Part53 (unitF53 radF53)

open BstLean.Part167
variable {n : ℕ}

noncomputable def operatorEnvelope160 (n : ℕ) : ℝ :=
  √(2 / (n : ℝ)) * (√((mA n : ℕ) : ℝ) + √(n : ℝ) + BstLean.Part152.gaussMomConst 80)

lemma operator_moment160 :
    ∫⁻ A₁, ENNReal.ofReal (opN A₁ ^ 160) ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal (operatorEnvelope160 n ^ 160) := by
  have hv : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  obtain ⟨hI, hB⟩ := BstLean.Part152.opN_moment (p := mA n) (q := n) hv (P := 80) (by norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun M =>
    pow_nonneg (opN_nonneg M) _)]
  exact ENNReal.ofReal_le_ofReal hB

/-- The one-sided Gaussian concentration constant at order 160. -/
noncomputable def transverseConstant160 : ℝ := BstLean.Part152.gaussMomConst 80

lemma transverseConstant_pos160 : 0 < transverseConstant160 := by
  unfold transverseConstant160 BstLean.Part152.gaussMomConst
  apply Real.rpow_pos_of_pos
  positivity

/-- **The assembly (the paper's Minkowski step for `K_ℓ`).** -/
theorem assemble_latitude160 {m : ℕ} {u w : Fin n → ℝ} (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (x : Fin n → ℝ) {v : ℝ} (hv : 0 < v)
    (G : Matrix (Fin m) (Fin n) ℝ → Fin m → ℝ)
    (Yf : Matrix (Fin m) (Fin n) ℝ → (Fin m → ℝ) × (Fin m → ℝ) → Fin m → ℝ)
    (hY1 : ∀ A₁ p, normSq (Yf A₁ p) ≤ 1) (μ : Measure (Matrix (Fin m) (Fin n) ℝ))
    [IsProbabilityMeasure μ]
    {X2 Y2 Zo : ℝ} (hX2 : 0 < X2) (hY2 : 0 < Y2) (hZo : 0 < Zo)
    (hX : ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (latSq (vecMul (planeP v (reluV (A₁ *ᵥ x))
        (G A₁) (gate (Yf A₁)) ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 80)
        ∂stdGauss (Fin m) ∂stdGauss (Fin m) ∂μ ≤ ENNReal.ofReal (X2 ^ 80))
    (hYm : Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => frobSq (Pmat u w * (D1A1 A₁ x)ᵀ)))
    (hY : ∫⁻ A₁, ENNReal.ofReal (frobSq (Pmat u w * (D1A1 A₁ x)ᵀ) ^ 80) ∂μ ≤
      ENNReal.ofReal (Y2 ^ 80))
    (hZ : ∫⁻ A₁, ENNReal.ofReal (opN A₁ ^ 160) ∂μ ≤ ENNReal.ofReal (Zo ^ 160)) :
    ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ γ, ENNReal.ofReal (latSq (vecMul (transRep v (reluV (A₁ *ᵥ x))
        (G A₁) (gate (Yf A₁)) ξ₁ ξ₂ γ) (D1A1 A₁ x)) u w ^ 80)
        ∂stdGauss (Fin m) ∂stdGauss (Fin m) ∂stdGauss (Fin m) ∂μ ≤
      ENNReal.ofReal ((√(X2 + v * Y2) + transverseConstant160 * √v * Zo) ^ 160) := by
  -- constants
  obtain ⟨A', hA'⟩ : ∃ A' : ℝ, A' = X2 + v * Y2 := ⟨_, rfl⟩
  have hA'0 : 0 < A' := by rw [hA']; positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = √A' := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; exact Real.sqrt_pos.mpr hA'0
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = transverseConstant160 * √v * Zo := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; have := transverseConstant_pos160; positivity
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = A + B := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨k₁, hk₁⟩ : ∃ k : ℝ, k = T ^ 159 / A ^ 159 * (A' ^ 79 / X2 ^ 79) := ⟨_, rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k : ℝ, k = T ^ 159 / A ^ 159 * (A' ^ 79 * v ^ 80 / (v * Y2) ^ 79) :=
    ⟨_, rfl⟩
  obtain ⟨k₃, hk₃⟩ : ∃ k : ℝ, k = T ^ 159 * (transverseConstant160 * √v) ^ 160 / B ^ 159 := ⟨_, rfl⟩
  have hk₁0 : 0 ≤ k₁ := by rw [hk₁]; positivity
  have hk₂0 : 0 ≤ k₂ := by rw [hk₂]; positivity
  have hk₃0 : 0 ≤ k₃ := by rw [hk₃]; have := transverseConstant_pos160; positivity
  -- the pointwise bound
  have hpt : ∀ (Np F o : ℝ), 0 ≤ Np → 0 ≤ F → 0 ≤ o →
      (√(Np + v * F) + transverseConstant160 * √v * o) ^ 160 ≤ k₁ * Np ^ 80 + k₂ * F ^ 80 + k₃ * o ^ 160 := by
    intro Np F o hNp hF ho
    have h1 := pow_add_split (Real.sqrt_nonneg (Np + v * F)) (by have := transverseConstant_pos160; positivity :
      0 ≤ transverseConstant160 * √v * o) hA0 hB0 159
    rw [← hT, show (159 : ℕ) + 1 = 160 from rfl] at h1
    have hs : √(Np + v * F) ^ 160 = (Np + v * F) ^ 80 := by
      rw [show (160 : ℕ) = 2 * 80 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
    rw [hs] at h1
    have h2 := pow_add_split hNp (by positivity : 0 ≤ v * F) hX2 (by positivity : 0 < v * Y2) 79
    rw [← hA', show (79 : ℕ) + 1 = 80 from rfl] at h2
    have h2' : (Np + v * F) ^ 80 / A ^ 159 ≤
        A' ^ 79 * (Np ^ 80 / X2 ^ 79 + (v * F) ^ 80 / (v * Y2) ^ 79) / A ^ 159 :=
      div_le_div_of_nonneg_right h2 (by positivity)
    have e3 : (transverseConstant160 * √v * o) ^ 160 / B ^ 159 = (transverseConstant160 * √v) ^ 160 * o ^ 160 / B ^ 159 := by
      rw [mul_pow]
    refine h1.trans ?_
    rw [e3]
    have h4 : T ^ 159 * ((Np + v * F) ^ 80 / A ^ 159 + (transverseConstant160 * √v) ^ 160 * o ^ 160 / B ^ 159) ≤
        T ^ 159 * (A' ^ 79 * (Np ^ 80 / X2 ^ 79 + (v * F) ^ 80 / (v * Y2) ^ 79) / A ^ 159 +
          (transverseConstant160 * √v) ^ 160 * o ^ 160 / B ^ 159) := by
      gcongr
    refine h4.trans (le_of_eq ?_)
    rw [hk₁, hk₂, hk₃, mul_pow v F]
    ring
  -- the inner integrals
  have hin : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ, ∀ ξ₁ ξ₂ : Fin m → ℝ,
      ∫⁻ γ, ENNReal.ofReal (latSq (vecMul (transRep v (reluV (A₁ *ᵥ x)) (G A₁) (gate (Yf A₁))
        ξ₁ ξ₂ γ) (D1A1 A₁ x)) u w ^ 80) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal (k₁ * latSq (vecMul (planeP v (reluV (A₁ *ᵥ x)) (G A₁) (gate (Yf A₁))
        ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 80) +
      ENNReal.ofReal (k₂ * frobSq (Pmat u w * (D1A1 A₁ x)ᵀ) ^ 80) +
      ENNReal.ofReal (k₃ * opN A₁ ^ 160) := by
    intro A₁ ξ₁ ξ₂
    simp_rw [transRep_eq]
    set W := gate (Yf A₁) (cOf v (reluV (A₁ *ᵥ x)) ξ₁, lam (reluV (A₁ *ᵥ x)) (G A₁) •
      cOf v (reluV (A₁ *ᵥ x)) ξ₁ + cOf v (res (reluV (A₁ *ᵥ x)) (G A₁)) ξ₂)
    set sv := √v * √(normSq W)
    have hsv0 : 0 ≤ sv := by positivity
    have hsv : sv ≤ √v := by
      have hW : normSq W ≤ 1 := (normSq_gate_le _ _).trans (hY1 _ _)
      have : √(normSq W) ≤ 1 := by
        rw [Real.sqrt_le_one]; exact hW
      calc sv ≤ √v * 1 := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
        _ = √v := mul_one _
    have hg := transverse_latitude160 hu hw huw (D1A1 A₁ x) (reluV (A₁ *ᵥ x)) (res (reluV (A₁ *ᵥ x)) (G A₁))
      (planeP v (reluV (A₁ *ᵥ x)) (G A₁) (gate (Yf A₁)) ξ₁ ξ₂) hsv0
    refine hg.trans ?_
    set Np := latSq (vecMul (planeP v (reluV (A₁ *ᵥ x)) (G A₁) (gate (Yf A₁)) ξ₁ ξ₂)
      (D1A1 A₁ x)) u w
    set F := frobSq (Pmat u w * (D1A1 A₁ x)ᵀ)
    have hNp : 0 ≤ Np := by
      simp only [Np]; rw [latSq_eq hu hw huw]; exact normSq_nonneg _
    have hF : 0 ≤ F := frobSq_nonneg _
    have ho := opN_nonneg A₁
    have hoD := opN_D1A1_le A₁ x
    have hmono : (√(Np + sv ^ 2 * F) + transverseConstant160 *
        (sv * opN (D1A1 A₁ x))) ^ 160 ≤ (√(Np + v * F) + transverseConstant160 * √v * opN A₁) ^ 160 := by
      have e1 : sv ^ 2 ≤ v := by
        have := pow_le_pow_left₀ hsv0 hsv 2
        rwa [Real.sq_sqrt hv.le] at this
      have h1 : √(Np + sv ^ 2 * F) ≤ √(Np + v * F) :=
        Real.sqrt_le_sqrt (by nlinarith)
      have h2 : sv * opN (D1A1 A₁ x) ≤ √v * opN A₁ :=
        mul_le_mul hsv hoD (opN_nonneg _) (Real.sqrt_nonneg _)
      have h3 : transverseConstant160 * (sv * opN (D1A1 A₁ x)) ≤
          transverseConstant160 * √v * opN A₁ := by
        rw [mul_assoc transverseConstant160]
        exact mul_le_mul_of_nonneg_left h2 transverseConstant_pos160.le
      have h0 : 0 ≤ √(Np + sv ^ 2 * F) + transverseConstant160 *
          (sv * opN (D1A1 A₁ x)) :=
        add_nonneg (Real.sqrt_nonneg _) (mul_nonneg transverseConstant_pos160.le
          (mul_nonneg hsv0 (opN_nonneg _)))
      exact pow_le_pow_left₀ h0 (add_le_add h1 h3) 160
    have p1 : 0 ≤ k₁ * Np ^ 80 := mul_nonneg hk₁0 (pow_nonneg hNp _)
    have p2 : 0 ≤ k₂ * F ^ 80 := mul_nonneg hk₂0 (pow_nonneg hF _)
    have p3 : 0 ≤ k₃ * opN A₁ ^ 160 := mul_nonneg hk₃0 (pow_nonneg ho _)
    rw [← ENNReal.ofReal_add p1 p2, ← ENNReal.ofReal_add (add_nonneg p1 p2) p3]
    exact ENNReal.ofReal_le_ofReal (hmono.trans (hpt Np F (opN A₁) hNp hF ho))
  have hadd : ∀ (f : (Fin m → ℝ) → ℝ≥0∞) (a b : ℝ≥0∞),
      ∫⁻ y, f y + a + b ∂stdGauss (Fin m) = ∫⁻ y, f y ∂stdGauss (Fin m) + a + b := by
    intro f a b
    rw [lintegral_add_right _ measurable_const, lintegral_add_right _ measurable_const]
    simp
  refine (lintegral_mono fun A₁ => lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ =>
    hin A₁ ξ₁ ξ₂).trans ?_
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Matrix (Fin m) (Fin n) ℝ → (Fin m → ℝ) → (Fin m → ℝ) → ℝ≥0∞,
      Φ = fun A₁ ξ₁ ξ₂ => ENNReal.ofReal (k₁ * latSq (vecMul (planeP v (reluV (A₁ *ᵥ x)) (G A₁)
        (gate (Yf A₁)) ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 80) := ⟨_, rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g : Matrix (Fin m) (Fin n) ℝ → ℝ≥0∞,
      g = fun A₁ => ENNReal.ofReal (k₂ * frobSq (Pmat u w * (D1A1 A₁ x)ᵀ) ^ 80) := ⟨_, rfl⟩
  obtain ⟨g₃, hg₃⟩ : ∃ g : Matrix (Fin m) (Fin n) ℝ → ℝ≥0∞,
      g = fun A₁ => ENNReal.ofReal (k₃ * opN A₁ ^ 160) := ⟨_, rfl⟩
  have hc : ∀ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, Φ A₁ ξ₁ ξ₂ + g₂ A₁ + g₃ A₁ ∂stdGauss (Fin m) ∂stdGauss (Fin m) =
      (∫⁻ ξ₁, ∫⁻ ξ₂, Φ A₁ ξ₁ ξ₂ ∂stdGauss (Fin m) ∂stdGauss (Fin m)) + g₂ A₁ + g₃ A₁ := fun A₁ =>
    (lintegral_congr fun ξ₁ => hadd (Φ A₁ ξ₁) (g₂ A₁) (g₃ A₁)).trans
      (hadd (fun ξ₁ => ∫⁻ ξ₂, Φ A₁ ξ₁ ξ₂ ∂stdGauss (Fin m)) (g₂ A₁) (g₃ A₁))
  have hgoal := lintegral_congr (μ := μ) hc
  rw [hΦ, hg₂, hg₃] at hgoal
  simp only at hgoal
  rw [hgoal]
  have hm2 : Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
      ENNReal.ofReal (k₂ * frobSq (Pmat u w * (D1A1 A₁ x)ᵀ) ^ 80)) :=
    ENNReal.measurable_ofReal.comp ((hYm.pow_const 80).const_mul _)
  have hm3 : Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => ENNReal.ofReal (k₃ * opN A₁ ^ 160)) :=
    ENNReal.measurable_ofReal.comp
      ((BstLean.Part152.opN_continuous.measurable.pow_const 160).const_mul _)
  rw [lintegral_add_right _ hm3, lintegral_add_right _ hm2]
  have e1 : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ, ∀ ξ₁ ξ₂ : Fin m → ℝ,
      ENNReal.ofReal (k₁ * latSq (vecMul (planeP v (reluV (A₁ *ᵥ x)) (G A₁) (gate (Yf A₁))
        ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 80) = ENNReal.ofReal k₁ *
      ENNReal.ofReal (latSq (vecMul (planeP v (reluV (A₁ *ᵥ x)) (G A₁) (gate (Yf A₁))
        ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 80) := fun _ _ _ => ENNReal.ofReal_mul hk₁0
  simp_rw [e1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have e2 : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal (k₂ * frobSq (Pmat u w *
      (D1A1 A₁ x)ᵀ) ^ 80) = ENNReal.ofReal k₂ *
        ENNReal.ofReal (frobSq (Pmat u w * (D1A1 A₁ x)ᵀ) ^ 80) := fun _ => ENNReal.ofReal_mul hk₂0
  have e3 : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal (k₃ * opN A₁ ^ 160) =
      ENNReal.ofReal k₃ * ENNReal.ofReal (opN A₁ ^ 160) := fun _ => ENNReal.ofReal_mul hk₃0
  simp_rw [e2, e3, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfin : k₁ * X2 ^ 80 + k₂ * Y2 ^ 80 + k₃ * Zo ^ 160 = T ^ 160 := by
    have hX : X2 ^ 80 / X2 ^ 79 = X2 := by rw [pow_succ X2 79]; field_simp
    have hYY : v ^ 80 * Y2 ^ 80 / (v * Y2) ^ 79 = v * Y2 := by
      rw [← mul_pow, pow_succ (v * Y2) 79]; field_simp
    have hAA : A' ^ 80 = A ^ 160 := by
      rw [hA, show (160 : ℕ) = 2 * 80 from rfl, pow_mul, Real.sq_sqrt hA'0.le]
    have hBB : (transverseConstant160 * √v) ^ 160 * Zo ^ 160 = B ^ 160 := by rw [hB, ← mul_pow]
    have s1 : k₁ * X2 ^ 80 + k₂ * Y2 ^ 80 =
        T ^ 159 / A ^ 159 * A' ^ 79 * (X2 ^ 80 / X2 ^ 79 + v ^ 80 * Y2 ^ 80 / (v * Y2) ^ 79) := by
      rw [hk₁, hk₂]; ring
    have s2 : k₃ * Zo ^ 160 = T ^ 159 * ((transverseConstant160 * √v) ^ 160 * Zo ^ 160 / B ^ 159) := by
      rw [hk₃]; ring
    rw [s1, s2, hX, hYY, ← hA', mul_assoc (T ^ 159 / A ^ 159), ← pow_succ, hAA, hBB, pow_succ A 159, pow_succ B 159]
    rw [show T ^ 159 / A ^ 159 * (A ^ 159 * A) = T ^ 159 * A by field_simp,
      show T ^ 159 * (B ^ 159 * B / B ^ 159) = T ^ 159 * B by field_simp, ← mul_add, ← hT,
      ← pow_succ]
  have p1 : 0 ≤ k₁ * X2 ^ 80 := mul_nonneg hk₁0 (pow_nonneg hX2.le _)
  have p2 : 0 ≤ k₂ * Y2 ^ 80 := mul_nonneg hk₂0 (pow_nonneg hY2.le _)
  have p3 : 0 ≤ k₃ * Zo ^ 160 := mul_nonneg hk₃0 (pow_nonneg hZo.le _)
  calc ENNReal.ofReal k₁ * ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (latSq (vecMul (planeP v
        (reluV (A₁ *ᵥ x)) (G A₁) (gate (Yf A₁)) ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 80)
        ∂stdGauss (Fin m) ∂stdGauss (Fin m) ∂μ +
      ENNReal.ofReal k₂ * ∫⁻ A₁, ENNReal.ofReal (frobSq (Pmat u w * (D1A1 A₁ x)ᵀ) ^ 80) ∂μ +
      ENNReal.ofReal k₃ * ∫⁻ A₁, ENNReal.ofReal (opN A₁ ^ 160) ∂μ
      ≤ ENNReal.ofReal k₁ * ENNReal.ofReal (X2 ^ 80) + ENNReal.ofReal k₂ * ENNReal.ofReal (Y2 ^ 80)
          + ENNReal.ofReal k₃ * ENNReal.ofReal (Zo ^ 160) := by gcongr
    _ = ENNReal.ofReal (T ^ 160) := by
        rw [← ENNReal.ofReal_mul hk₁0, ← ENNReal.ofReal_mul hk₂0, ← ENNReal.ofReal_mul hk₃0,
          ← ENNReal.ofReal_add p1 p2, ← ENNReal.ofReal_add (add_nonneg p1 p2) p3, hfin]
    _ = ENNReal.ofReal ((√(X2 + v * Y2) + transverseConstant160 * √v * Zo) ^ 160) := by rw [hT, hA, hB, hA']

end BstLean.Part212
