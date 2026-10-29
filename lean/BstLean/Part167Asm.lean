import BstLean.Part167Gam

/-!
# Part 167 (file `Asm`): Lemma LJ reduced to the plane moment `X` and the masked Frobenius moment `Y`

No proof is left open; no `native_decide` or `axiom` is used.

Paper: Lemma `t7:p07:LJ`, `K_ℓ = √(X_ℓ² + Y_ℓ²) + Z_ℓ`. For a World value in the window, an
index `a` and a direction `v ≠ 0` (unit input `x`, frame `(u, w)`), and an admissible direction
`Y` (`b̂` or `r̂`):

* `planeP`: the plane part `p = α₁h₁ + α₂r` of `A₂ᵀD₂y` (file `Split`); `NpF`: `|P_lat (D₁A₁)ᵀp|²`;
  `FrA`: `‖P_lat (D₁A₁)ᵀ‖²_F` (the paper's `‖M₀‖²_HS`).
* **`asm_core`**: if `E_{A₁,ξ} NpF^{64} ≤ X2^{64}` and `E_{A₁} FrA^{64} ≤ Y2^{64}`, then the
  moment in `JM_hyp` is at most `(√(X2 + t_A·Y2) + C√t_A·Zop)^{128}`, with
  `Zop = √(2/n)(√m + √n + g₆₄)` from Part 152's `opN_moment` (proved, the paper's `Z_ℓ`).
* **`JM_of_XY`**: `JM_hyp n K2` from the two moment hypotheses `XY_hyp` for `y = b̂` and `y = r̂`.
-/

namespace BstLean.Part167

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

variable {n : ℕ}

/-- The plane part `p = α₁h + α₂r` of the representation `transRep`. -/
noncomputable def planeP {q m : ℕ} (v : ℝ) (h g : Fin m → ℝ)
    (W : (Fin q → ℝ) × (Fin q → ℝ) → Fin q → ℝ) (ξ₁ ξ₂ : Fin q → ℝ) : Fin m → ℝ :=
  ((normSq h)⁻¹ * ∑ i, W (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂) i *
      cOf v h ξ₁ i) • h +
    ((normSq (res h g))⁻¹ * ∑ i,
      W (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂) i * cOf v (res h g) ξ₂ i) •
        res h g

lemma transRep_eq {q m : ℕ} (v : ℝ) (h g : Fin m → ℝ)
    (W : (Fin q → ℝ) × (Fin q → ℝ) → Fin q → ℝ) (ξ₁ ξ₂ : Fin q → ℝ) (γ : Fin m → ℝ) :
    transRep v h g W ξ₁ ξ₂ γ = planeP v h g W ξ₁ ξ₂ +
      perp h (perp (res h g) ((√v * √(normSq
        (W (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂)))) • γ)) := by
  unfold transRep planeP
  rw [perp_plane, add_assoc]

/-- The orthonormal frame `(u, w)` of a direction `v ≠ 0`. -/
lemma frame_orth (hn : 1 ≤ n) {c : Fin n → ℝ} (hc : c ≠ 0) {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    normSq (uHat (rc c)) = 1 ∧ normSq (dirW (rc c) (unitF53 v)) = 1 ∧
      ∑ i, uHat (rc c) i * dirW (rc c) (unitF53 v) i = 0 := by
  have hc' : (rc c).1.2 ≠ 0 := hc
  refine ⟨BstLean.Part161.normSq_uHat hc', ?_, ?_⟩
  · unfold dirW
    rw [BstLean.Part161.hh_normSq, BstLean.Part161.normSq_consV hn]
    have h1 : normSq (unitF53 v) = radF53 (unitF53 v) ^ 2 := (BstLean.Part162.radF_sq _).symm
    rw [h1, BstLean.Part162.radF_unitF hv]; ring
  · have h := BstLean.Part161.dir_orth hn hc' (unitF53 v)
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by unfold dirW; ring

lemma opN_D1A1_le {m k : ℕ} (A₁ : Matrix (Fin m) (Fin k) ℝ) (x : Fin k → ℝ) :
    opN (D1A1 A₁ x) ≤ opN A₁ := by
  refine BstLean.Part153.opN_le_of_bound _ (opN_nonneg A₁) fun z => ?_
  have e : D1A1 A₁ x *ᵥ z = fun i => mask ((A₁ *ᵥ x) i) * (A₁ *ᵥ z) i := by
    funext i; simp only [D1A1, mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact (BstLean.Part153.nrm_mask_mul_le _ _).trans (nrm_mulVec_le A₁ z)

lemma normSq_gate_le {m : ℕ} (Y : (Fin m → ℝ) × (Fin m → ℝ) → Fin m → ℝ) (p) :
    normSq (gate Y p) ≤ normSq (Y p) := by
  unfold gate normSq
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_pow, BstLean.Part151.mask_sq]
  have h1 : mask (p.1 j) ≤ 1 := mask_le_one _
  nlinarith [sq_nonneg (Y p j), BstLean.Part151.mask_nonneg (p.1 j)]

lemma normSq_bhat_le {m : ℕ} (b : Fin m → ℝ) : normSq (bhat b) ≤ 1 := by
  rcases bhat_cases b with h | h
  · rw [h]; simp [normSq]
  · rw [h]

/-- The moment of `opN A₁` (Part 152's `opN_moment`, `P = 64`). -/
noncomputable def Zop (n : ℕ) : ℝ :=
  √(2 / (n : ℝ)) * (√((mA n : ℕ) : ℝ) + √(n : ℝ) + BstLean.Part152.gaussMomConst 64)

lemma Zop_mom :
    ∫⁻ A₁, ENNReal.ofReal (opN A₁ ^ 128) ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal (Zop n ^ 128) := by
  have hv : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  obtain ⟨hI, hB⟩ := BstLean.Part152.opN_moment (p := mA n) (q := n) hv (P := 64) (by norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun M =>
    pow_nonneg (opN_nonneg M) _)]
  exact ENNReal.ofReal_le_ofReal hB

/-- The constant of the transverse step, `(π/2)(E|g|^{128})^{1/128}`. -/
noncomputable def Cg : ℝ := π / 2 * BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128)

lemma Cg_pos : 0 < Cg := by
  have hg : 0 < BstLean.Part162.gmom 128 := by
    rw [show (128 : ℕ) = 2 * 64 by norm_num, BstLean.Part162.gmom_even]
    exact Finset.prod_pos fun j _ => by positivity
  exact mul_pos (by positivity) (Real.rpow_pos_of_pos hg _)

/-- **The assembly (the paper's Minkowski step for `K_ℓ`).** -/
theorem asm_core {m : ℕ} {u w : Fin n → ℝ} (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (x : Fin n → ℝ) {v : ℝ} (hv : 0 < v)
    (G : Matrix (Fin m) (Fin n) ℝ → Fin m → ℝ)
    (Yf : Matrix (Fin m) (Fin n) ℝ → (Fin m → ℝ) × (Fin m → ℝ) → Fin m → ℝ)
    (hY1 : ∀ A₁ p, normSq (Yf A₁ p) ≤ 1) (μ : Measure (Matrix (Fin m) (Fin n) ℝ))
    [IsProbabilityMeasure μ]
    {X2 Y2 Zo : ℝ} (hX2 : 0 < X2) (hY2 : 0 < Y2) (hZo : 0 < Zo)
    (hX : ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (latSq (vecMul (planeP v (reluV (A₁ *ᵥ x))
        (G A₁) (gate (Yf A₁)) ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 64)
        ∂stdGauss (Fin m) ∂stdGauss (Fin m) ∂μ ≤ ENNReal.ofReal (X2 ^ 64))
    (hYm : Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => frobSq (Pmat u w * (D1A1 A₁ x)ᵀ)))
    (hY : ∫⁻ A₁, ENNReal.ofReal (frobSq (Pmat u w * (D1A1 A₁ x)ᵀ) ^ 64) ∂μ ≤
      ENNReal.ofReal (Y2 ^ 64))
    (hZ : ∫⁻ A₁, ENNReal.ofReal (opN A₁ ^ 128) ∂μ ≤ ENNReal.ofReal (Zo ^ 128)) :
    ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ γ, ENNReal.ofReal (latSq (vecMul (transRep v (reluV (A₁ *ᵥ x))
        (G A₁) (gate (Yf A₁)) ξ₁ ξ₂ γ) (D1A1 A₁ x)) u w ^ 64)
        ∂stdGauss (Fin m) ∂stdGauss (Fin m) ∂stdGauss (Fin m) ∂μ ≤
      ENNReal.ofReal ((√(X2 + v * Y2) + Cg * √v * Zo) ^ 128) := by
  -- constants
  obtain ⟨A', hA'⟩ : ∃ A' : ℝ, A' = X2 + v * Y2 := ⟨_, rfl⟩
  have hA'0 : 0 < A' := by rw [hA']; positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = √A' := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; exact Real.sqrt_pos.mpr hA'0
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = Cg * √v * Zo := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; have := Cg_pos; positivity
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = A + B := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨k₁, hk₁⟩ : ∃ k : ℝ, k = T ^ 127 / A ^ 127 * (A' ^ 63 / X2 ^ 63) := ⟨_, rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k : ℝ, k = T ^ 127 / A ^ 127 * (A' ^ 63 * v ^ 64 / (v * Y2) ^ 63) :=
    ⟨_, rfl⟩
  obtain ⟨k₃, hk₃⟩ : ∃ k : ℝ, k = T ^ 127 * (Cg * √v) ^ 128 / B ^ 127 := ⟨_, rfl⟩
  have hk₁0 : 0 ≤ k₁ := by rw [hk₁]; positivity
  have hk₂0 : 0 ≤ k₂ := by rw [hk₂]; positivity
  have hk₃0 : 0 ≤ k₃ := by rw [hk₃]; have := Cg_pos; positivity
  -- the pointwise bound
  have hpt : ∀ (Np F o : ℝ), 0 ≤ Np → 0 ≤ F → 0 ≤ o →
      (√(Np + v * F) + Cg * √v * o) ^ 128 ≤ k₁ * Np ^ 64 + k₂ * F ^ 64 + k₃ * o ^ 128 := by
    intro Np F o hNp hF ho
    have h1 := pow_add_split (Real.sqrt_nonneg (Np + v * F)) (by have := Cg_pos; positivity :
      0 ≤ Cg * √v * o) hA0 hB0 127
    rw [← hT, show (127 : ℕ) + 1 = 128 from rfl] at h1
    have hs : √(Np + v * F) ^ 128 = (Np + v * F) ^ 64 := by
      rw [show (128 : ℕ) = 2 * 64 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
    rw [hs] at h1
    have h2 := pow_add_split hNp (by positivity : 0 ≤ v * F) hX2 (by positivity : 0 < v * Y2) 63
    rw [← hA', show (63 : ℕ) + 1 = 64 from rfl] at h2
    have h2' : (Np + v * F) ^ 64 / A ^ 127 ≤
        A' ^ 63 * (Np ^ 64 / X2 ^ 63 + (v * F) ^ 64 / (v * Y2) ^ 63) / A ^ 127 :=
      div_le_div_of_nonneg_right h2 (by positivity)
    have e3 : (Cg * √v * o) ^ 128 / B ^ 127 = (Cg * √v) ^ 128 * o ^ 128 / B ^ 127 := by
      rw [mul_pow]
    refine h1.trans ?_
    rw [e3]
    have h4 : T ^ 127 * ((Np + v * F) ^ 64 / A ^ 127 + (Cg * √v) ^ 128 * o ^ 128 / B ^ 127) ≤
        T ^ 127 * (A' ^ 63 * (Np ^ 64 / X2 ^ 63 + (v * F) ^ 64 / (v * Y2) ^ 63) / A ^ 127 +
          (Cg * √v) ^ 128 * o ^ 128 / B ^ 127) := by
      gcongr
    refine h4.trans (le_of_eq ?_)
    rw [hk₁, hk₂, hk₃, mul_pow v F]
    ring
  -- the inner integrals
  have hin : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ, ∀ ξ₁ ξ₂ : Fin m → ℝ,
      ∫⁻ γ, ENNReal.ofReal (latSq (vecMul (transRep v (reluV (A₁ *ᵥ x)) (G A₁) (gate (Yf A₁))
        ξ₁ ξ₂ γ) (D1A1 A₁ x)) u w ^ 64) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal (k₁ * latSq (vecMul (planeP v (reluV (A₁ *ᵥ x)) (G A₁) (gate (Yf A₁))
        ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 64) +
      ENNReal.ofReal (k₂ * frobSq (Pmat u w * (D1A1 A₁ x)ᵀ) ^ 64) +
      ENNReal.ofReal (k₃ * opN A₁ ^ 128) := by
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
    have hg := gamma_step hu hw huw (D1A1 A₁ x) (reluV (A₁ *ᵥ x)) (res (reluV (A₁ *ᵥ x)) (G A₁))
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
    have hmono : (√(Np + sv ^ 2 * F) + π / 2 * BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) *
        (sv * opN (D1A1 A₁ x))) ^ 128 ≤ (√(Np + v * F) + Cg * √v * opN A₁) ^ 128 := by
      have e1 : sv ^ 2 ≤ v := by
        have := pow_le_pow_left₀ hsv0 hsv 2
        rwa [Real.sq_sqrt hv.le] at this
      have h1 : √(Np + sv ^ 2 * F) ≤ √(Np + v * F) :=
        Real.sqrt_le_sqrt (by nlinarith)
      have h2 : sv * opN (D1A1 A₁ x) ≤ √v * opN A₁ :=
        mul_le_mul hsv hoD (opN_nonneg _) (Real.sqrt_nonneg _)
      have h3 : π / 2 * BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) * (sv * opN (D1A1 A₁ x)) ≤
          Cg * √v * opN A₁ := by
        rw [mul_assoc Cg]
        exact mul_le_mul_of_nonneg_left h2 Cg_pos.le
      have h0 : 0 ≤ √(Np + sv ^ 2 * F) + π / 2 * BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) *
          (sv * opN (D1A1 A₁ x)) :=
        add_nonneg (Real.sqrt_nonneg _) (mul_nonneg Cg_pos.le
          (mul_nonneg hsv0 (opN_nonneg _)))
      exact pow_le_pow_left₀ h0 (add_le_add h1 h3) 128
    have p1 : 0 ≤ k₁ * Np ^ 64 := mul_nonneg hk₁0 (pow_nonneg hNp _)
    have p2 : 0 ≤ k₂ * F ^ 64 := mul_nonneg hk₂0 (pow_nonneg hF _)
    have p3 : 0 ≤ k₃ * opN A₁ ^ 128 := mul_nonneg hk₃0 (pow_nonneg ho _)
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
        (gate (Yf A₁)) ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 64) := ⟨_, rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g : Matrix (Fin m) (Fin n) ℝ → ℝ≥0∞,
      g = fun A₁ => ENNReal.ofReal (k₂ * frobSq (Pmat u w * (D1A1 A₁ x)ᵀ) ^ 64) := ⟨_, rfl⟩
  obtain ⟨g₃, hg₃⟩ : ∃ g : Matrix (Fin m) (Fin n) ℝ → ℝ≥0∞,
      g = fun A₁ => ENNReal.ofReal (k₃ * opN A₁ ^ 128) := ⟨_, rfl⟩
  have hc : ∀ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, Φ A₁ ξ₁ ξ₂ + g₂ A₁ + g₃ A₁ ∂stdGauss (Fin m) ∂stdGauss (Fin m) =
      (∫⁻ ξ₁, ∫⁻ ξ₂, Φ A₁ ξ₁ ξ₂ ∂stdGauss (Fin m) ∂stdGauss (Fin m)) + g₂ A₁ + g₃ A₁ := fun A₁ =>
    (lintegral_congr fun ξ₁ => hadd (Φ A₁ ξ₁) (g₂ A₁) (g₃ A₁)).trans
      (hadd (fun ξ₁ => ∫⁻ ξ₂, Φ A₁ ξ₁ ξ₂ ∂stdGauss (Fin m)) (g₂ A₁) (g₃ A₁))
  have hgoal := lintegral_congr (μ := μ) hc
  rw [hΦ, hg₂, hg₃] at hgoal
  simp only at hgoal
  rw [hgoal]
  have hm2 : Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
      ENNReal.ofReal (k₂ * frobSq (Pmat u w * (D1A1 A₁ x)ᵀ) ^ 64)) :=
    ENNReal.measurable_ofReal.comp ((hYm.pow_const 64).const_mul _)
  have hm3 : Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => ENNReal.ofReal (k₃ * opN A₁ ^ 128)) :=
    ENNReal.measurable_ofReal.comp
      ((BstLean.Part152.opN_continuous.measurable.pow_const 128).const_mul _)
  rw [lintegral_add_right _ hm3, lintegral_add_right _ hm2]
  have e1 : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ, ∀ ξ₁ ξ₂ : Fin m → ℝ,
      ENNReal.ofReal (k₁ * latSq (vecMul (planeP v (reluV (A₁ *ᵥ x)) (G A₁) (gate (Yf A₁))
        ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 64) = ENNReal.ofReal k₁ *
      ENNReal.ofReal (latSq (vecMul (planeP v (reluV (A₁ *ᵥ x)) (G A₁) (gate (Yf A₁))
        ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 64) := fun _ _ _ => ENNReal.ofReal_mul hk₁0
  simp_rw [e1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have e2 : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal (k₂ * frobSq (Pmat u w *
      (D1A1 A₁ x)ᵀ) ^ 64) = ENNReal.ofReal k₂ *
        ENNReal.ofReal (frobSq (Pmat u w * (D1A1 A₁ x)ᵀ) ^ 64) := fun _ => ENNReal.ofReal_mul hk₂0
  have e3 : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal (k₃ * opN A₁ ^ 128) =
      ENNReal.ofReal k₃ * ENNReal.ofReal (opN A₁ ^ 128) := fun _ => ENNReal.ofReal_mul hk₃0
  simp_rw [e2, e3, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfin : k₁ * X2 ^ 64 + k₂ * Y2 ^ 64 + k₃ * Zo ^ 128 = T ^ 128 := by
    have hX : X2 ^ 64 / X2 ^ 63 = X2 := by rw [pow_succ X2 63]; field_simp
    have hYY : v ^ 64 * Y2 ^ 64 / (v * Y2) ^ 63 = v * Y2 := by
      rw [← mul_pow, pow_succ (v * Y2) 63]; field_simp
    have hAA : A' ^ 64 = A ^ 128 := by
      rw [hA, show (128 : ℕ) = 2 * 64 from rfl, pow_mul, Real.sq_sqrt hA'0.le]
    have hBB : (Cg * √v) ^ 128 * Zo ^ 128 = B ^ 128 := by rw [hB, ← mul_pow]
    have s1 : k₁ * X2 ^ 64 + k₂ * Y2 ^ 64 =
        T ^ 127 / A ^ 127 * A' ^ 63 * (X2 ^ 64 / X2 ^ 63 + v ^ 64 * Y2 ^ 64 / (v * Y2) ^ 63) := by
      rw [hk₁, hk₂]; ring
    have s2 : k₃ * Zo ^ 128 = T ^ 127 * ((Cg * √v) ^ 128 * Zo ^ 128 / B ^ 127) := by
      rw [hk₃]; ring
    rw [s1, s2, hX, hYY, ← hA', mul_assoc (T ^ 127 / A ^ 127), ← pow_succ, hAA, hBB, pow_succ A 127, pow_succ B 127]
    rw [show T ^ 127 / A ^ 127 * (A ^ 127 * A) = T ^ 127 * A by field_simp,
      show T ^ 127 * (B ^ 127 * B / B ^ 127) = T ^ 127 * B by field_simp, ← mul_add, ← hT,
      ← pow_succ]
  have p1 : 0 ≤ k₁ * X2 ^ 64 := mul_nonneg hk₁0 (pow_nonneg hX2.le _)
  have p2 : 0 ≤ k₂ * Y2 ^ 64 := mul_nonneg hk₂0 (pow_nonneg hY2.le _)
  have p3 : 0 ≤ k₃ * Zo ^ 128 := mul_nonneg hk₃0 (pow_nonneg hZo.le _)
  calc ENNReal.ofReal k₁ * ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (latSq (vecMul (planeP v
        (reluV (A₁ *ᵥ x)) (G A₁) (gate (Yf A₁)) ξ₁ ξ₂) (D1A1 A₁ x)) u w ^ 64)
        ∂stdGauss (Fin m) ∂stdGauss (Fin m) ∂μ +
      ENNReal.ofReal k₂ * ∫⁻ A₁, ENNReal.ofReal (frobSq (Pmat u w * (D1A1 A₁ x)ᵀ) ^ 64) ∂μ +
      ENNReal.ofReal k₃ * ∫⁻ A₁, ENNReal.ofReal (opN A₁ ^ 128) ∂μ
      ≤ ENNReal.ofReal k₁ * ENNReal.ofReal (X2 ^ 64) + ENNReal.ofReal k₂ * ENNReal.ofReal (Y2 ^ 64)
          + ENNReal.ofReal k₃ * ENNReal.ofReal (Zo ^ 128) := by gcongr
    _ = ENNReal.ofReal (T ^ 128) := by
        rw [← ENNReal.ofReal_mul hk₁0, ← ENNReal.ofReal_mul hk₂0, ← ENNReal.ofReal_mul hk₃0,
          ← ENNReal.ofReal_add p1 p2, ← ENNReal.ofReal_add (add_nonneg p1 p2) p3, hfin]
    _ = ENNReal.ofReal ((√(X2 + v * Y2) + Cg * √v * Zo) ^ 128) := by rw [hT, hA, hB, hA']

end BstLean.Part167
