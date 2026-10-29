import BstLean.Part170FlQ

/-!
# Part 170 (file `DecW`): the exact-rule energy error = fluctuation + bias, at a fixed `A₁`

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, `nΔ_ω^exact = N_ω^fl + N_ω^b` and formula `t7:p08:energy`.

* `exWn_eq`: `exWn = Σ_j E_v ReLU((M a₁(x_v))_j)² − Σ_j E_Z ReLU((Mā)_j + ςZ)²`.
* `exWn_Mpl`: at fixed plane coordinates, `exWn = Q(N) − C₀` with `Q = flQ` of file `FlQ`.
* `M0_bound`: `|M₀ y|² ≤ t|y|²(|ξ₁|² + |ξ₂|²)` (Bessel in the plane).
* `biasW c g ξ₁ ξ₂ = E_N exWn`: **the conditional mean of the exact-rule energy error given the
  plane coordinates** (the paper's `nΔ_ω^b`).
* **`exWn_mom`**: on `‖A₁‖_op ≤ O`, at a node with `s² ≤ 1`, if `E_{ξ₁,ξ₂} biasW⁸ ≤ B⁸`, then
  `E_{A₂} exWn⁸ ≤ (W_fl + B)⁸`, `W_fl = a₁ + b₁√3√(m + 8)`,
  `a₁ = (2.5c√(tΛ))² + 2c₈√(tΛ) + (c√(tΛ))²`, `b₁ = 2c₈√(tΛ)·√(tO²)`, `c = π/2`,
  `c₈ = 1.8π/2`, `Λ = O²/(n − 2)`.
-/

namespace BstLean.Part170

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part53 (unitF53 measurable_unitF)
open BstLean.Part134 (res lam projPerp glue)
open BstLean.Part167 (perp normSq_perp_le)
open BstLean.Part162 (gmom gmom_nonneg)
open BstLean.Part157 (cOf reb)

variable {n : ℕ}

/-- The Gaussian second moment `G₂(y) = E_Z ReLU(y + ςZ)²` of the energy pass. -/
noncomputable def G2 (σ y : ℝ) : ℝ := ∫ z, relu (y + σ * z) ^ 2 ∂gaussianReal 0 1

lemma exWn_eq (hn : 1 ≤ n) (c : Ret n) (g : ℕ) {K : ℝ}
    (hK : ∀ v, ‖aLat c (nodeS c g) v‖ ≤ K) (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :
    exWn (withA2 c M) g = ∑ j, ∫ v, relu ((M *ᵥ aLat c (nodeS c g) v) j) ^ 2
        ∂stdGauss (Fin (n - 1)) -
      ∑ j, G2 √(vsig2 c (nodeS c g)) ((M *ᵥ a1Bar c (nodeS c g)) j) := by
  set s := nodeS c g
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hint : ∀ j, Integrable (fun v => relu ((M *ᵥ aLat c s v) j) ^ 2)
      (stdGauss (Fin (n - 1))) := fun j =>
    int_comp_bdd (f := fun y => relu ((M *ᵥ y) j) ^ 2) (measurable_aLat c s) hK
      ((continuous_relu.comp ((continuous_apply j).comp (Continuous.matrix_mulVec
        continuous_const continuous_id))).pow 2)
  have hw : wbarS (withA2 c M) s = (∑ j, ∫ v, relu ((M *ᵥ aLat c s v) j) ^ 2
      ∂stdGauss (Fin (n - 1))) / (n : ℝ) := by
    have e : ∀ v, wX (withA2 c M) (xLat (withA2 c M) s (unitF53 v)) =
        (∑ j, relu ((M *ᵥ aLat c s v) j) ^ 2) / (n : ℝ) := fun v => rfl
    unfold wbarS
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_div,
      integral_finsetSum _ fun j _ => hint j]
  have hg : wGauss (withA2 c M) s = (∑ j, G2 √(vsig2 c s) ((M *ᵥ a1Bar c s) j)) / (n : ℝ) := rfl
  unfold exWn
  rw [show nodeS (withA2 c M) g = s from rfl, hw, hg]
  field_simp

lemma exWn_Mpl (hn : 1 ≤ n) (c : Ret n) (g : ℕ) {K : ℝ}
    (hK : ∀ v, ‖aLat c (nodeS c g) v‖ ≤ K) (c₁ c₂ : Fin (mA n) → ℝ)
    (N : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :
    exWn (withA2 c (Mpl (hB c) (res (hB c) (a1Bar c (nodeS c g))) c₁ c₂ N)) g =
      flQ (stdGauss (Fin (n - 1))) (aLat c (nodeS c g)) (hB c)
        (Mpl (hB c) (res (hB c) (a1Bar c (nodeS c g))) c₁ c₂ 0) N -
      ∑ j, G2 √(vsig2 c (nodeS c g))
        ((Mpl (hB c) (res (hB c) (a1Bar c (nodeS c g))) c₁ c₂ 0 *ᵥ a1Bar c (nodeS c g)) j) := by
  set s := nodeS c g
  set h := hB c
  set r := res h (a1Bar c s)
  rw [exWn_eq hn c g hK]
  have ea : Mpl h r c₁ c₂ N *ᵥ a1Bar c s = Mpl h r c₁ c₂ 0 *ᵥ a1Bar c s := by
    rw [Mpl_mulVec, perp_perp_res, Matrix.mulVec_zero, add_zero]
  rw [ea]
  unfold flQ
  rw [vmean_aLat]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [Mpl_mulVec]
  rfl

/-! ## The plane part of the second layer -/

lemma normSq_perp_eq (b z : Fin (mA n) → ℝ) :
    normSq (perp b z) = normSq z - (normSq b)⁻¹ * (∑ j, z j * b j) ^ 2 := by
  unfold perp
  set B := normSq b
  set cz := ∑ j, z j * b j
  have e1 : normSq (z - (B⁻¹ * cz) • b) = normSq z - 2 * (B⁻¹ * cz) * cz + (B⁻¹ * cz) ^ 2 * B := by
    unfold normSq
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have e : ∀ i, (z i - B⁻¹ * cz * b i) ^ 2 = z i ^ 2 - 2 * (B⁻¹ * cz) * (z i * b i) +
        (B⁻¹ * cz) ^ 2 * b i ^ 2 := fun i => by ring
    simp_rw [e]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  rw [e1]
  by_cases hB : B = 0
  · rw [hB]; simp
  · field_simp; ring

lemma normSq_add_le' (u w : Fin (mA n) → ℝ) :
    normSq (u + w) ≤ (√(normSq u) + √(normSq w)) ^ 2 := by
  have h := abs_dot_le u w
  have hu : 0 ≤ normSq u := by unfold normSq; positivity
  have hw : 0 ≤ normSq w := by unfold normSq; positivity
  have e : normSq (u + w) = normSq u + normSq w + 2 * (u ⬝ᵥ w) := by
    unfold normSq dotProduct
    simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  rw [e, add_sq, Real.sq_sqrt hu, Real.sq_sqrt hw]
  have := le_abs_self (u ⬝ᵥ w)
  nlinarith

/-- **The plane part of the second layer**: `|M₀ y|² ≤ t|y|²(|ξ₁|² + |ξ₂|²)`. -/
lemma M0_bound {t : ℝ} (ht : 0 ≤ t) (h a : Fin (mA n) → ℝ) (ξ₁ ξ₂ y : Fin (mA n) → ℝ) :
    normSq (Mpl h (res h a) (cOf t h ξ₁) (cOf t (res h a) ξ₂) 0 *ᵥ y) ≤
      t * normSq y * (normSq ξ₁ + normSq ξ₂) := by
  set r := res h a
  set α := (normSq h)⁻¹ * ∑ k, y k * h k
  set β := (normSq r)⁻¹ * ∑ k, perp h y k * r k
  have hM : Mpl h r (cOf t h ξ₁) (cOf t r ξ₂) 0 *ᵥ y =
      (α * (√t * √(normSq h))) • ξ₁ + (β * (√t * √(normSq r))) • ξ₂ := by
    unfold Mpl reb glue cOf
    simp only [Matrix.zero_mul, add_zero, Matrix.add_mulVec, Matrix.smul_mulVec,
      BstLean.Part167.vmv_mulVec, ← Matrix.mulVec_mulVec, BstLean.Part167.projPerp_mulVec, smul_smul]
    simp only [α, β, mul_assoc]
  set p := α * (√t * √(normSq h))
  set q := β * (√t * √(normSq r))
  have hp : p ^ 2 = t * ((normSq h)⁻¹ * (∑ k, y k * h k) ^ 2) := by
    simp only [p, α]
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt (by unfold normSq; positivity)]
    by_cases hh : normSq h = 0
    · rw [hh]; simp
    · field_simp
  have hq : q ^ 2 = t * ((normSq r)⁻¹ * (∑ k, perp h y k * r k) ^ 2) := by
    simp only [q, β]
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt (by unfold normSq; positivity)]
    by_cases hh : normSq r = 0
    · rw [hh]; simp
    · field_simp
  have hpy : (normSq r)⁻¹ * (∑ k, perp h y k * r k) ^ 2 ≤ normSq (perp h y) := by
    have := normSq_perp_eq r (perp h y)
    have h0 : 0 ≤ normSq (perp r (perp h y)) := by unfold normSq; positivity
    linarith
  have hpq : p ^ 2 + q ^ 2 ≤ t * normSq y := by
    rw [hp, hq]
    have := normSq_perp_eq h y
    nlinarith
  rw [hM]
  refine (normSq_add_le' _ _).trans ?_
  rw [BstLean.Part130.normSq_smul, BstLean.Part130.normSq_smul, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  set a1 := √(normSq ξ₁)
  set a2 := √(normSq ξ₂)
  have ha1 : a1 ^ 2 = normSq ξ₁ := Real.sq_sqrt (by unfold normSq; positivity)
  have ha2 : a2 ^ 2 = normSq ξ₂ := Real.sq_sqrt (by unfold normSq; positivity)
  have hcs : (|p| * a1 + |q| * a2) ^ 2 ≤ (p ^ 2 + q ^ 2) * (a1 ^ 2 + a2 ^ 2) := by
    nlinarith [sq_nonneg (|p| * a2 - |q| * a1), sq_abs p, sq_abs q]
  rw [ha1, ha2] at hcs
  calc (|p| * a1 + |q| * a2) ^ 2 ≤ (p ^ 2 + q ^ 2) * (normSq ξ₁ + normSq ξ₂) := hcs
    _ ≤ t * normSq y * (normSq ξ₁ + normSq ξ₂) :=
        mul_le_mul_of_nonneg_right hpq (by unfold normSq; positivity)

/-! ## The eighth moment of the energy error -/

lemma aLat_normSq_le (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {O : ℝ}
    (h1 : OpB (A1 c) O) (v : Fin (n - 1) → ℝ) : normSq (aLat c s v) ≤ O ^ 2 := by
  unfold aLat
  refine (BstLean.Part131.normSq_reluV_le _).trans ((h1 _).trans ?_)
  have := normSq_xLat_le' hn c hs v
  nlinarith [sq_nonneg O]

/-- **The conditional mean of the exact-rule energy error given the plane coordinates.** -/
noncomputable def biasW (c : Ret n) (g : ℕ) (ξ₁ ξ₂ : Fin (mA n) → ℝ) : ℝ :=
  ∫ N, exWn (withA2 c (Mpl (hB c) (res (hB c) (a1Bar c (nodeS c g)))
    (cOf (tA n) (hB c) ξ₁) (cOf (tA n) (res (hB c) (a1Bar c (nodeS c g))) ξ₂) N)) g
    ∂gaussMat (mA n) (mA n) (tA n)

/-- The energy fluctuation allowance `W_fl = a₁ + b₁√3√(m + 8)`. -/
noncomputable def Wfl (n : ℕ) (O : ℝ) : ℝ :=
  ((π / 2 * (25 / 10) * √(tA n * (O ^ 2 / ((n : ℝ) - 2)))) ^ 2 +
    2 * (π / 2 * (18 / 10) * √(tA n * (O ^ 2 / ((n : ℝ) - 2)))) +
    (π / 2 * √(tA n * (O ^ 2 / ((n : ℝ) - 2)))) ^ 2) +
  2 * (π / 2 * (18 / 10) * √(tA n * (O ^ 2 / ((n : ℝ) - 2)))) * √(tA n * O ^ 2) *
    (√3 * √((mA n : ℝ) + 8))

lemma pow4_three {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x + y + z) ^ 4 ≤ 27 * (x ^ 4 + y ^ 4 + z ^ 4) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z), sq_nonneg (x + y - 2 * z),
    sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (x ^ 2 - z ^ 2),
    mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hx hz, sq_nonneg (x + y + z),
    mul_nonneg (mul_nonneg hx hy) hz]

/-- `E (|ξ₁|² + |ξ₂|² + m)⁴ ≤ 81(m + 8)⁴`. -/
lemma chi_two_mom (m : ℕ) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((normSq ξ₁ + normSq ξ₂ + m) ^ 4) ∂stdGauss (Fin m)
      ∂stdGauss (Fin m) ≤ ENNReal.ofReal (81 * ((m : ℝ) + 8) ^ 4) := by
  have hc : ∀ k : ℕ, ∫⁻ ξ, ENNReal.ofReal ((normSq ξ) ^ k) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal (((m : ℝ) + 2 * k) ^ k) := fun k => by
    have := BstLean.Part166.chi_mom (ι := Fin m) k
    simp only [Fintype.card_fin] at this
    exact this
  have hpt : ∀ ξ₁ ξ₂ : Fin m → ℝ, ENNReal.ofReal ((normSq ξ₁ + normSq ξ₂ + m) ^ 4) ≤
      ENNReal.ofReal 27 * ENNReal.ofReal ((normSq ξ₁) ^ 4) +
      ENNReal.ofReal 27 * ENNReal.ofReal ((normSq ξ₂) ^ 4) +
      ENNReal.ofReal (27 * (m : ℝ) ^ 4) := fun ξ₁ ξ₂ => by
    have h1 : 0 ≤ normSq ξ₁ := by unfold normSq; positivity
    have h2 : 0 ≤ normSq ξ₂ := by unfold normSq; positivity
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := pow4_three h1 h2 (Nat.cast_nonneg m)
    linarith
  have m4 : Measurable (fun ξ : Fin m → ℝ => ENNReal.ofReal ((normSq ξ) ^ 4)) :=
    ENNReal.measurable_ofReal.comp (continuous_normSq.measurable.pow_const 4)
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((normSq ξ₁ + normSq ξ₂ + m) ^ 4) ∂stdGauss (Fin m)
        ∂stdGauss (Fin m)
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, (ENNReal.ofReal 27 * ENNReal.ofReal ((normSq ξ₁) ^ 4) +
          ENNReal.ofReal 27 * ENNReal.ofReal ((normSq ξ₂) ^ 4) +
          ENNReal.ofReal (27 * (m : ℝ) ^ 4)) ∂stdGauss (Fin m) ∂stdGauss (Fin m) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hpt ξ₁ ξ₂
    _ = ENNReal.ofReal 27 * ∫⁻ ξ, ENNReal.ofReal ((normSq ξ) ^ 4) ∂stdGauss (Fin m) +
          ENNReal.ofReal 27 * ∫⁻ ξ, ENNReal.ofReal ((normSq ξ) ^ 4) ∂stdGauss (Fin m) +
          ENNReal.ofReal (27 * (m : ℝ) ^ 4) := by
        have e1 : ∀ ξ₁ : Fin m → ℝ, ∫⁻ ξ₂, (ENNReal.ofReal 27 * ENNReal.ofReal ((normSq ξ₁) ^ 4) +
            ENNReal.ofReal 27 * ENNReal.ofReal ((normSq ξ₂) ^ 4) +
            ENNReal.ofReal (27 * (m : ℝ) ^ 4)) ∂stdGauss (Fin m) =
            ENNReal.ofReal 27 * ENNReal.ofReal ((normSq ξ₁) ^ 4) +
            ENNReal.ofReal 27 * ∫⁻ ξ, ENNReal.ofReal ((normSq ξ) ^ 4) ∂stdGauss (Fin m) +
            ENNReal.ofReal (27 * (m : ℝ) ^ 4) := fun ξ₁ => by
          rw [lintegral_add_right _ measurable_const, lintegral_add_left measurable_const,
            lintegral_const, lintegral_const, measure_univ, mul_one, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp_rw [e1]
        rw [lintegral_add_right _ measurable_const, lintegral_add_right _ measurable_const,
          lintegral_const, lintegral_const, measure_univ, mul_one, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal 27 * ENNReal.ofReal (((m : ℝ) + 2 * 4) ^ 4) +
          ENNReal.ofReal 27 * ENNReal.ofReal (((m : ℝ) + 2 * 4) ^ 4) +
          ENNReal.ofReal (27 * (m : ℝ) ^ 4) := by
        have h4 := hc 4
        push_cast at h4
        gcongr
    _ ≤ ENNReal.ofReal (81 * ((m : ℝ) + 8) ^ 4) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have : (m : ℝ) ^ 4 ≤ ((m : ℝ) + 8) ^ 4 := pow_le_pow_left₀ hm (by linarith) 4
        nlinarith

/-- `E_{ξ₁,ξ₂}(a₁ + b₁√(|ξ₁|² + |ξ₂|² + m))⁸ ≤ (a₁ + b₁√3√(m + 8))⁸`. -/
lemma outer_mom (m : ℕ) {a₁ b₁ : ℝ} (ha : 0 < a₁) (hb : 0 < b₁) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ + m)) ^ 8)
      ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((a₁ + b₁ * (√3 * √((m : ℝ) + 8))) ^ 8) := by
  set B₁ := b₁ * (√3 * √((m : ℝ) + 8))
  have hB₁ : 0 < B₁ := by positivity
  set k₃ := (a₁ + B₁) ^ 7 / a₁ ^ 7
  set k₄ := (a₁ + B₁) ^ 7 / B₁ ^ 7
  have hk₃ : 0 ≤ k₃ := by positivity
  have hk₄ : 0 ≤ k₄ := by positivity
  have hX : ∀ ξ₁ ξ₂ : Fin m → ℝ, 0 ≤ normSq ξ₁ + normSq ξ₂ + m := fun ξ₁ ξ₂ => by
    unfold normSq; positivity
  have hpt : ∀ ξ₁ ξ₂ : Fin m → ℝ, ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ + m)) ^ 8) ≤
      ENNReal.ofReal (k₃ * a₁ ^ 8) + ENNReal.ofReal (k₄ * b₁ ^ 8) *
        ENNReal.ofReal ((normSq ξ₁ + normSq ξ₂ + m) ^ 4) := fun ξ₁ ξ₂ => by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := pow8_split a₁ (b₁ * √(normSq ξ₁ + normSq ξ₂ + m)) ha hB₁
    rw [abs_of_pos ha, abs_of_nonneg (by positivity)] at h
    have e : (b₁ * √(normSq ξ₁ + normSq ξ₂ + m)) ^ 8 = b₁ ^ 8 * (normSq ξ₁ + normSq ξ₂ + m) ^ 4 := by
      rw [mul_pow, show (8 : ℕ) = 2 * 4 from rfl, pow_mul (√_), Real.sq_sqrt (hX ξ₁ ξ₂)]
    rw [e] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ + m)) ^ 8)
        ∂stdGauss (Fin m) ∂stdGauss (Fin m)
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, (ENNReal.ofReal (k₃ * a₁ ^ 8) + ENNReal.ofReal (k₄ * b₁ ^ 8) *
          ENNReal.ofReal ((normSq ξ₁ + normSq ξ₂ + m) ^ 4)) ∂stdGauss (Fin m) ∂stdGauss (Fin m) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hpt ξ₁ ξ₂
    _ = ENNReal.ofReal (k₃ * a₁ ^ 8) + ENNReal.ofReal (k₄ * b₁ ^ 8) * ∫⁻ ξ₁, ∫⁻ ξ₂,
          ENNReal.ofReal ((normSq ξ₁ + normSq ξ₂ + m) ^ 4) ∂stdGauss (Fin m) ∂stdGauss (Fin m) := by
        have e1 : ∀ ξ₁ : Fin m → ℝ, ∫⁻ ξ₂, (ENNReal.ofReal (k₃ * a₁ ^ 8) +
            ENNReal.ofReal (k₄ * b₁ ^ 8) * ENNReal.ofReal ((normSq ξ₁ + normSq ξ₂ + m) ^ 4))
            ∂stdGauss (Fin m) = ENNReal.ofReal (k₃ * a₁ ^ 8) + ENNReal.ofReal (k₄ * b₁ ^ 8) *
              ∫⁻ ξ₂, ENNReal.ofReal ((normSq ξ₁ + normSq ξ₂ + m) ^ 4) ∂stdGauss (Fin m) := fun ξ₁ => by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp_rw [e1]
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (k₃ * a₁ ^ 8) + ENNReal.ofReal (k₄ * b₁ ^ 8) *
          ENNReal.ofReal (81 * ((m : ℝ) + 8) ^ 4) := by
        gcongr; exact chi_two_mom m
    _ = ENNReal.ofReal ((a₁ + B₁) ^ 8) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have e : B₁ ^ 8 = b₁ ^ 8 * (81 * ((m : ℝ) + 8) ^ 4) := by
          simp only [B₁]
          rw [mul_pow, mul_pow, show (8 : ℕ) = 2 * 4 from rfl, pow_mul (√3), pow_mul (√((m:ℝ) + 8)),
            Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
          ring
        have hA7 : a₁ ^ 7 ≠ 0 := by positivity
        have hB7 : B₁ ^ 7 ≠ 0 := by positivity
        rw [show k₄ * b₁ ^ 8 * (81 * ((m : ℝ) + 8) ^ 4) = k₄ * B₁ ^ 8 by rw [e]; ring]
        simp only [k₃, k₄]
        field_simp

/-- **The eighth moment of the exact-rule energy error over `A₂`, at a fixed `A₁`**: on
`‖A₁‖_op ≤ O`, at a node with `s_g² ≤ 1`, if the bias (the conditional mean given the plane
coordinates) has `E_{ξ₁,ξ₂} biasW⁸ ≤ B⁸`, then `E_{A₂} exWn⁸ ≤ (W_fl + B)⁸`. -/
theorem exWn_mom (hn : 3 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 < O)
    (h1 : OpB (A1 c) O) {B : ℝ} (hB0 : 0 < B)
    (hBias : ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
      ∂stdGauss (Fin (mA n)) ≤ ENNReal.ofReal (B ^ 8)) :
    ∫⁻ M, ENNReal.ofReal (exWn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal ((Wfl n O + B) ^ 8) := by
  have hn1 : 1 ≤ n := by omega
  set s := nodeS c g with hsd
  set h := hB c
  set r := res h (a1Bar c s)
  set Λ := O ^ 2 / ((n : ℝ) - 2) with hΛd
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hΛ0 : 0 < Λ := by positivity
  have htA : 0 < tA n := by
    unfold tA; have : 0 < mA n := by unfold mA; positivity
    positivity
  have hK := aLat_bdd hn1 c hs hO.le h1
  have hK2 : ∀ v, normSq (aLat c s v) ≤ O ^ 2 := aLat_normSq_le hn1 c hs h1
  have hΛ : ∀ e, ∫ v, (e ⬝ᵥ (aLat c s v - vmean (stdGauss (Fin (n - 1))) (aLat c s))) ^ 2
      ∂stdGauss (Fin (n - 1)) ≤ Λ * normSq e := cov_bound hn c hs hO.le h1
  set L := √(tA n * Λ) with hLd
  have hL : 0 < L := Real.sqrt_pos.mpr (mul_pos htA hΛ0)
  set a₁ := (π / 2 * (25 / 10) * L) ^ 2 + 2 * (π / 2 * (18 / 10) * L) + (π / 2 * L) ^ 2
  set b₁ := 2 * (π / 2 * (18 / 10) * L) * √(tA n * O ^ 2)
  have ha₁ : 0 < a₁ := by positivity
  have hb₁ : 0 < b₁ := by
    have : 0 < √(tA n * O ^ 2) := Real.sqrt_pos.mpr (by positivity)
    positivity
  set A := Wfl n O with hAd
  have hAe : A = a₁ + b₁ * (√3 * √((mA n : ℝ) + 8)) := by rw [hAd]; unfold Wfl; rfl
  have hA : 0 < A := by rw [hAe]; positivity
  set k₁ := (A + B) ^ 7 / A ^ 7
  set k₂ := (A + B) ^ 7 / B ^ 7
  have hk₁ : 0 ≤ k₁ := by positivity
  have hk₂ : 0 ≤ k₂ := by positivity
  -- the plane split
  have mF : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => ENNReal.ofReal (exWn (withA2 c p.2.2) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exWn_comp ((measurable_withA2 c).comp
      (measurable_snd.comp measurable_snd)) measurable_const).pow_const 8)
  have hps := BstLean.Part167.plane_split (q := mA n) (tA n) h (a1Bar c s) mF
  have e0 : ∫⁻ M, ENNReal.ofReal (exWn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) =
      ∫⁻ M, (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
        ENNReal.ofReal (exWn (withA2 c p.2.2) g ^ 8)) (M *ᵥ h, M *ᵥ a1Bar c s, M)
        ∂gaussMat (mA n) (mA n) (tA n) := rfl
  rw [e0, hps]
  simp only
  -- the inner bound at fixed plane coordinates
  have hin : ∀ ξ₁ ξ₂ : Fin (mA n) → ℝ, ∫⁻ N, ENNReal.ofReal (exWn (withA2 c
      (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
      ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ + (mA n : ℝ))) ^ 8) +
        ENNReal.ofReal k₂ * ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) := by
    intro ξ₁ ξ₂
    set c₁ := cOf (tA n) h ξ₁
    set c₂ := cOf (tA n) r ξ₂
    set M₀ := Mpl h r c₁ c₂ 0
    set C₀ := ∑ j, G2 √(vsig2 c s) ((M₀ *ᵥ a1Bar c s) j)
    set E : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ := fun N =>
      exWn (withA2 c (reb h c₁ (reb r c₂ N))) g
    have mE : Measurable E :=
      measurable_exWn_comp ((measurable_withA2 c).comp (BstLean.Part157.measurable_reb_comp
        measurable_const measurable_const (BstLean.Part157.measurable_reb_comp measurable_const
          measurable_const measurable_id))) measurable_const
    have hE : ∀ N, E N = flQ (stdGauss (Fin (n - 1))) (aLat c s) h M₀ N - C₀ := fun N =>
      exWn_Mpl hn1 c g hK c₁ c₂ N
    set F : (Fin (mA n) × Fin (mA n) → ℝ) → ℝ := fun ζ =>
      flQ (stdGauss (Fin (n - 1))) (aLat c s) h M₀ (matOf (tA n) ζ)
    have hS := sqrtQ_euLip (measurable_aLat c s) hK hΛ0.le hΛ h M₀ htA.le
    have iF : Integrable F (stdGauss (Fin (mA n) × Fin (mA n))) := by
      have := euLip_sq_integrable (Real.sqrt_nonneg _) hS
      refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
      exact Real.sq_sqrt (flQ_nonneg _ _ _ _)
    set qb := ∫ ζ, F ζ ∂stdGauss (Fin (mA n) × Fin (mA n))
    have hmE : biasW c g ξ₁ ξ₂ = qb - C₀ := by
      have e0 : biasW c g ξ₁ ξ₂ = ∫ N, E N ∂gaussMat (mA n) (mA n) (tA n) := rfl
      rw [e0, gaussMat_eq, integral_map (measurable_matOf _).aemeasurable mE.aestronglyMeasurable]
      have : (fun ζ => E (matOf (tA n) ζ)) = fun ζ => F ζ - C₀ := funext fun ζ => hE _
      rw [this]
      rw [integral_sub iF (integrable_const _)]
      simp
      rfl
    -- `qb ≤ tO²(X + m)`
    have hqb : qb ≤ tA n * O ^ 2 * (normSq ξ₁ + normSq ξ₂ + (mA n : ℝ)) := by
      have hα : ∀ v, normSq (M₀ *ᵥ aLat c s v) ≤ tA n * O ^ 2 * (normSq ξ₁ + normSq ξ₂) := fun v =>
        (M0_bound htA.le h (a1Bar c s) ξ₁ ξ₂ (aLat c s v)).trans (by
          have hX : 0 ≤ normSq ξ₁ + normSq ξ₂ := by unfold normSq; positivity
          have := mul_le_mul_of_nonneg_left (hK2 v) htA.le
          nlinarith)
      have := flQ_mean_le (measurable_aLat c s) hK hΛ0.le hΛ h M₀ htA.le
        (by unfold normSq; positivity) (sq_nonneg O) hα hK2
      calc qb ≤ _ := this
        _ = _ := by ring
    have hfl := flQ_conc (measurable_aLat c s) hK hΛ0 hΛ h M₀ htA
    have hFl : (π / 2 * (25 / 10) * L) ^ 2 + 2 * (√qb + 1) * (π / 2 * (18 / 10) * L) +
        (π / 2 * L) ^ 2 ≤ a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ + (mA n : ℝ)) := by
      have h1' : √qb ≤ √(tA n * O ^ 2) * √(normSq ξ₁ + normSq ξ₂ + (mA n : ℝ)) := by
        rw [← Real.sqrt_mul (by positivity)]; exact Real.sqrt_le_sqrt hqb
      have hc8 : 0 ≤ π / 2 * (18 / 10) * L := by positivity
      have := mul_le_mul_of_nonneg_left h1' (by positivity : (0:ℝ) ≤ 2 * (π / 2 * (18 / 10) * L))
      simp only [a₁, b₁]
      nlinarith
    have hpt : ∀ ζ, ENNReal.ofReal (E (matOf (tA n) ζ) ^ 8) ≤ ENNReal.ofReal k₁ *
        ENNReal.ofReal (|F ζ - qb| ^ 8) + ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
      intro ζ
      rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_add (by positivity)
        (mul_nonneg hk₂ (by positivity))]
      refine ENNReal.ofReal_le_ofReal ?_
      have := pow8_split (F ζ - qb) (biasW c g ξ₁ ξ₂) hA hB0
      have e8 : |biasW c g ξ₁ ξ₂| ^ 8 = biasW c g ξ₁ ξ₂ ^ 8 := (by decide : Even 8).pow_abs _
      rw [e8] at this
      have e : E (matOf (tA n) ζ) = F ζ - qb + biasW c g ξ₁ ξ₂ := by rw [hE, hmE]; ring
      rw [e]; exact this
    have cF : Continuous F :=
      ((hS.continuous (Real.sqrt_nonneg _)).pow 2).congr fun ζ => Real.sq_sqrt (flQ_nonneg _ _ _ _)
    have mfl : Measurable (fun ζ => ENNReal.ofReal (|F ζ - qb| ^ 8)) :=
      ENNReal.measurable_ofReal.comp (((cF.measurable.sub_const _).abs).pow_const 8)
    rw [gaussMat_eq, lintegral_map (f := fun N => ENNReal.ofReal (E N ^ 8))
      (ENNReal.measurable_ofReal.comp (mE.pow_const 8)) (measurable_matOf _)]
    calc ∫⁻ ζ, ENNReal.ofReal (E (matOf (tA n) ζ) ^ 8) ∂stdGauss (Fin (mA n) × Fin (mA n))
        ≤ ∫⁻ ζ, (ENNReal.ofReal k₁ * ENNReal.ofReal (|F ζ - qb| ^ 8) +
          ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8)) ∂stdGauss (Fin (mA n) × Fin (mA n)) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal k₁ * ∫⁻ ζ, ENNReal.ofReal (|F ζ - qb| ^ 8)
            ∂stdGauss (Fin (mA n) × Fin (mA n)) + ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ mfl]
      _ ≤ ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ +
            (mA n : ℝ))) ^ 8) + ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
          gcongr
          refine hfl.trans (ENNReal.ofReal_le_ofReal ?_)
          exact pow_le_pow_left₀ (by positivity) hFl 8
      _ = _ := by rw [ENNReal.ofReal_mul hk₂]
  -- the outer integrals
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N, ENNReal.ofReal (exWn (withA2 c
        (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
        ∂gaussMat (mA n) (mA n) (tA n) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, (ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ +
          (mA n : ℝ))) ^ 8) + ENNReal.ofReal k₂ * ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8))
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hin ξ₁ ξ₂
    _ = ENNReal.ofReal k₁ * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ +
          (mA n : ℝ))) ^ 8) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) +
          ENNReal.ofReal k₂ * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8)
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) := by
        have mI : ∀ ξ₁ : Fin (mA n) → ℝ, Measurable (fun ξ₂ : Fin (mA n) → ℝ =>
            ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ +
              (mA n : ℝ))) ^ 8)) := fun ξ₁ =>
          measurable_const.mul (ENNReal.measurable_ofReal.comp ((measurable_const.add
            (measurable_const.mul (((measurable_const.add continuous_normSq.measurable).add
              measurable_const).sqrt))).pow_const 8))
        have e1 : ∀ ξ₁ : Fin (mA n) → ℝ, ∫⁻ ξ₂, (ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ *
            √(normSq ξ₁ + normSq ξ₂ + (mA n : ℝ))) ^ 8) + ENNReal.ofReal k₂ *
            ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8)) ∂stdGauss (Fin (mA n)) =
            ENNReal.ofReal k₁ * ∫⁻ ξ₂, ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ +
              (mA n : ℝ))) ^ 8) ∂stdGauss (Fin (mA n)) + ENNReal.ofReal k₂ *
            ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n)) := fun ξ₁ => by
          rw [lintegral_add_left (mI ξ₁), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp_rw [e1]
        have mJ : Measurable (fun ξ₁ : Fin (mA n) → ℝ => ENNReal.ofReal k₁ * ∫⁻ ξ₂,
            ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ + (mA n : ℝ))) ^ 8)
            ∂stdGauss (Fin (mA n))) := by
          refine measurable_const.mul ?_
          exact (ENNReal.measurable_ofReal.comp ((measurable_const.add
            (measurable_const.mul ((((continuous_normSq.measurable.comp measurable_fst).add
              (continuous_normSq.measurable.comp measurable_snd)).add
              measurable_const).sqrt))).pow_const 8) : Measurable (fun p :
            (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) => ENNReal.ofReal ((a₁ + b₁ * √(normSq p.1 +
              normSq p.2 + (mA n : ℝ))) ^ 8))).lintegral_prod_right'
        rw [lintegral_add_left mJ, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal k₁ * ENNReal.ofReal (A ^ 8) + ENNReal.ofReal k₂ * ENNReal.ofReal (B ^ 8) := by
        gcongr
        rw [hAe]; exact outer_mom (mA n) ha₁ hb₁
    _ = ENNReal.ofReal ((A + B) ^ 8) := by
        rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_mul hk₂,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have hA7 : A ^ 7 ≠ 0 := by positivity
        have hB7 : B ^ 7 ≠ 0 := by positivity
        simp only [k₁, k₂]
        field_simp

end BstLean.Part170
