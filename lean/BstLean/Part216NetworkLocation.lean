import BstLean.Part216Location
import BstLean.Part173Cov

/-! Location order24 for the actual conditional passes, from dimension three. -/
namespace BstLean.Part216
open MeasureTheory ProbabilityTheory Real Filter Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170
open BstLean.Part134 (res)
open BstLean.Part157 (cOf)

variable {n : ℕ}

noncomputable def locationPassFluct (c : Ret n) (g : ℕ)
    (ξ₁ ξ₂ : Fin (mA n) → ℝ) (N : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) : ℝ :=
  exFn (withA2 c
    (reb (hB c) (cOf (tA n) (hB c) ξ₁)
      (reb (res (hB c) (a1Bar c (nodeS c g)))
        (cOf (tA n) (res (hB c) (a1Bar c (nodeS c g))) ξ₂) N))) g - biasF c g ξ₁ ξ₂

/-- The centred location moment at one network node has no first-layer dimension floor
beyond the covariance construction. No transverse event restriction enters the integral. -/
theorem network_location24 (hn : 3 ≤ n) (c : Ret n) (g : ℕ)
    (hs : nodeS c g ^ 2 ≤ 1) {O q : ℝ} (hO : 0 ≤ O) (h1 : OpB (A1 c) O)
    (hq0 : 0 ≤ q) (hq : 1 - nodeS c g ^ 2 ≤ q)
    (ξ₁ ξ₂ : Fin (mA n) → ℝ) :
    ∫⁻ N, ENNReal.ofReal (|exFn (withA2 c
        (reb (hB c) (cOf (tA n) (hB c) ξ₁)
          (reb (res (hB c) (a1Bar c (nodeS c g)))
            (cOf (tA n) (res (hB c) (a1Bar c (nodeS c g))) ξ₂) N))) g -
      biasF c g ξ₁ ξ₂| ^ 24) ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal (2 * (sqrt (n : ℝ) *
        sqrt (tA n * (q * O ^ 2 / ((n : ℝ) - 2))) / 2) ^ 24 *
          (2 ^ 12 * ((12 : ℕ).factorial : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  let s := nodeS c g
  let h := hB c
  let r := res h (a1Bar c s)
  let Λ := q * O ^ 2 / ((n : ℝ) - 2)
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - 2 := by linarith
  have hΛ0 : 0 ≤ Λ := by dsimp [Λ]; positivity
  have htA : 0 ≤ tA n := by unfold tA; positivity
  have hK := aLat_bdd hn1 c hs hO h1
  have hΛ : ∀ e, ∫ v, (e ⬝ᵥ (aLat c s v -
      vmean (stdGauss (Fin (n - 1))) (aLat c s))) ^ 2 ∂stdGauss (Fin (n - 1)) ≤
        Λ * normSq e := fun e =>
    (BstLean.Part173.cov_bound_lat hn c hs hO h1 e).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hq (sq_nonneg O)) hden.le) (normSq_nonneg e))
  let c₁ := cOf (tA n) h ξ₁
  let c₂ := cOf (tA n) r ξ₂
  let M₀ := Mpl h r c₁ c₂ 0
  let b := bOfY c (M₀ *ᵥ h)
  let ψ : Fin (mA n) → ℝ := fun j =>
    BstLean.Part137.psiS (sqrt (vsig2 c s)) ((M₀ *ᵥ a1Bar c s) j)
  let κ := (n : ℝ) / (sqrt (n : ℝ) * sqrt (normSq b))
  let E := flE (stdGauss (Fin (n - 1))) (aLat c s) h M₀ b ψ κ
  have he : ∀ N, exFn (withA2 c (reb h c₁ (reb r c₂ N))) g = E N :=
    fun N => exFn_Mpl hn1 c g hK c₁ c₂ N
  have hm : ∫ N, E N ∂gaussMat (mA n) (mA n) (tA n) = biasF c g ξ₁ ξ₂ := by
    unfold biasF
    exact integral_congr_ae (Eventually.of_forall fun N => (he N).symm)
  have hfl := location_order24 (measurable_aLat c s) hK hΛ0 hΛ h M₀ b ψ κ htA
  have hL : |κ| * sqrt (normSq b) * sqrt (tA n * Λ) / 2 ≤
      sqrt (n : ℝ) * sqrt (tA n * Λ) / 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (kappa_b_le n b)
      (sqrt_nonneg _)) (by norm_num)
  change (∫⁻ N, ENNReal.ofReal (|exFn (withA2 c (reb h c₁ (reb r c₂ N))) g -
    biasF c g ξ₁ ξ₂| ^ 24) ∂gaussMat (mA n) (mA n) (tA n)) ≤ _
  simp_rw [he, ← hm]
  refine hfl.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hL 24) (by norm_num))
    (by positivity)

#print axioms network_location24

/-- Integrating both retained plane arrays adds no event restriction or charge. -/
theorem network_location24_planes (hn : 3 ≤ n) (c : Ret n) (g : ℕ)
    (hs : nodeS c g ^ 2 ≤ 1) {O q : ℝ} (hO : 0 ≤ O) (h1 : OpB (A1 c) O)
    (hq0 : 0 ≤ q) (hq : 1 - nodeS c g ^ 2 ≤ q) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N, ENNReal.ofReal (|locationPassFluct c g ξ₁ ξ₂ N| ^ 24)
      ∂gaussMat (mA n) (mA n) (tA n) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ≤
      ENNReal.ofReal (2 * (sqrt (n : ℝ) *
        sqrt (tA n * (q * O ^ 2 / ((n : ℝ) - 2))) / 2) ^ 24 *
          (2 ^ 12 * ((12 : ℕ).factorial : ℝ))) := by
  have hnode := fun ξ₁ ξ₂ => network_location24 hn c g hs hO h1 hq0 hq ξ₁ ξ₂
  calc _ ≤ ∫⁻ _ξ₁ : Fin (mA n) → ℝ, ∫⁻ _ξ₂ : Fin (mA n) → ℝ,
      ENNReal.ofReal (2 * (sqrt (n : ℝ) *
        sqrt (tA n * (q * O ^ 2 / ((n : ℝ) - 2))) / 2) ^ 24 *
          (2 ^ 12 * ((12 : ℕ).factorial : ℝ)))
        ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) :=
    lintegral_mono fun ξ₁ => lintegral_mono (hnode ξ₁)
    _ = _ := by simp

#print axioms network_location24_planes
end BstLean.Part216
