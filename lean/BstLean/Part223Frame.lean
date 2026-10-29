import BstLean.Part223Polar
import BstLean.Part172Frm

namespace BstLean.Part223
open BstLean.Part172 BstLean.Part212

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part151 (mask)
open BstLean.Part161 (uHat xLat)
open BstLean.Part162 (dirW)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part167 (latSq D1A1 Aframe eprime gaussMat_frame frame_reads latSq_vecMul_frame)

variable {n : ℕ}

theorem fr_frame256 (hn : 4 ≤ n) {q : ℕ} (hq : 1 ≤ q) {u w : Fin n → ℝ} {s cs : ℝ}
    (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (hsc : s ^ 2 + cs ^ 2 = 1)
    (e : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (hadm : ∀ A A' : Matrix (Fin (mA n)) (Fin n) ℝ, A *ᵥ (s • u + cs • w) = A' *ᵥ (s • u + cs • w) →
      A *ᵥ u = A' *ᵥ u → (∀ i, ∑ j, A i j ^ 2 = ∑ j, A' i j ^ 2) → e A = e A')
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ A, normSq (e A) ≤ B) :
    ∫⁻ A₁, ENNReal.ofReal (latSq (vecMul (e A₁) (D1A1 A₁ (s • u + cs • w))) u w ^ 128)
        ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal (radialProduct (n - 1 - 1) 128 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 128 *
        (2 / (n : ℝ) * B) ^ 128 *
        ((((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / q) * (((n - 1 - 1 : ℕ) : ℝ) + 256 * q) ^ 128))) := by
  have hn2 : 2 ≤ n := by omega
  have hd : 2 ≤ n - 1 - 1 := by omega
  have hm0 : 0 < mA n := by unfold mA; have : 0 < n := by omega
                            positivity
  have hγ : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  rw [gaussMat_frame hn2 (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs)]
  have hmeas : Measurable (Aframe (m := mA n) (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs)) :=
    BstLean.Part168.measurable_Aframe _ _ _
  refine (lintegral_map_le _ hmeas.aemeasurable).trans ?_
  have hrw : ∀ W, ENNReal.ofReal (latSq (vecMul (e (Aframe (2 / (n : ℝ)) (s • u + cs • w)
      (eprime hn2 u w s cs) W)) (D1A1 (Aframe (2 / (n : ℝ)) (s • u + cs • w)
      (eprime hn2 u w s cs) W) (s • u + cs • w))) u w ^ 128) =
      ENNReal.ofReal (normSq (∑ i, fr_kap hn2 u w s cs e W i • (W i).2.2) ^ 128) := by
    intro W
    rw [latSq_vecMul_frame hn2 hu hw huw hsc (2 / (n : ℝ)) W]
    simp only [fr_kap]
  rw [lintegral_congr hrw]
  have hinv : ∀ W W' : Fin (mA n) → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ), (∀ i, (W i).1 = (W' i).1 ∧
      (W i).2.1 = (W' i).2.1 ∧ normSq (W i).2.2 = normSq (W' i).2.2) →
      fr_kap hn2 u w s cs e W = fr_kap hn2 u w s cs e W' := by
    intro W W' h
    have fr := frame_reads (m := mA n) hn2 hu hw huw hsc hγ W
    have fr' := frame_reads (m := mA n) hn2 hu hw huw hsc hγ W'
    have hAx : Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W *ᵥ (s • u + cs • w) =
        Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W' *ᵥ (s • u + cs • w) := by
      funext i; rw [(fr i).1, (fr' i).1, (h i).1]
    have hAu : Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W *ᵥ u =
        Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W' *ᵥ u := by
      funext i; rw [(fr i).2.1, (fr' i).2.1, (h i).1, (h i).2.1]
    have hrow : ∀ i, ∑ j, Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W i j ^ 2 =
        ∑ j, Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W' i j ^ 2 := by
      intro i; rw [(fr i).2.2, (fr' i).2.2, (h i).1, (h i).2.1, (h i).2.2]
    have he := hadm _ _ hAx hAu hrow
    unfold fr_kap
    rw [he, hAx]
  have hkB : ∀ W, normSq (fr_kap hn2 u w s cs e W) ≤ 2 / (n : ℝ) * B := by
    intro W
    unfold fr_kap normSq
    have : ∀ i, (√(2 / (n : ℝ)) *
        e (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W) i *
        mask ((Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W *ᵥ (s • u + cs • w)) i)) ^ 2
        ≤ 2 / (n : ℝ) * e (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W) i ^ 2 := by
      intro i
      rw [mul_pow, mul_pow, Real.sq_sqrt hγ, BstLean.Part151.mask_sq]
      have h1 := BstLean.Part167.mask_le_one ((Aframe (2 / (n : ℝ)) (s • u + cs • w)
        (eprime hn2 u w s cs) W *ᵥ (s • u + cs • w)) i)
      have h0 := BstLean.Part151.mask_nonneg ((Aframe (2 / (n : ℝ)) (s • u + cs • w)
        (eprime hn2 u w s cs) W *ᵥ (s • u + cs • w)) i)
      have : 0 ≤ 2 / (n : ℝ) * e (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W) i ^ 2 := by
        positivity
      nlinarith
    refine (Finset.sum_le_sum fun i _ => this i).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hB _) hγ
  have hP := polar_core256 hm0 hd hq (fr_kap hn2 u w s cs e) hinv
    (mul_nonneg hγ hB0) hkB
  refine hP.trans (le_of_eq ?_)
  congr 1


/-- **The frame moment of a first-layer tangential statistic** for an admissible direction
`e` with `|e|² ≤ B`: `E_{A₁} latSq((D₁A₁)ᵀe)^{128} ≤ K_d (γB)^{128} m^{1/q}(d+256q)^{128}`. -/
theorem frame_mom256 (hn : 4 ≤ n) {q : ℕ} (hq : 1 ≤ q) {c : Ret n} (hc : c.1.2 ≠ 0) {s : ℝ}
    (hs : s ^ 2 ≤ 1) {v : Fin (n - 1) → ℝ} (hv : v ≠ 0)
    (e : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (hadm : ∀ A A' : Matrix (Fin (mA n)) (Fin n) ℝ, A *ᵥ xLat c s (unitF53 v) =
      A' *ᵥ xLat c s (unitF53 v) → A *ᵥ uHat c = A' *ᵥ uHat c →
      (∀ i, ∑ j, A i j ^ 2 = ∑ j, A' i j ^ 2) → e A = e A')
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ A, normSq (e A) ≤ B) :
    ∫⁻ A₁, ENNReal.ofReal (latSq (vecMul (e A₁) (D1A1 A₁ (xLat c s (unitF53 v)))) (uHat c)
        (dirW c (unitF53 v)) ^ 128) ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal (radialProduct (n - 1 - 1) 128 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 128 *
        (2 / (n : ℝ) * B) ^ 128 *
        ((((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / q) * (((n - 1 - 1 : ℕ) : ℝ) + 256 * q) ^ 128))) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hu, hw, huw⟩ := fr_orth hn1 hc hv
  have hsc : s ^ 2 + √(1 - s ^ 2) ^ 2 = 1 := by rw [Real.sq_sqrt (by linarith)]; ring
  rw [fr_xLat hn1 hc] at hadm ⊢
  exact fr_frame256 hn hq hu hw huw hsc e hadm hB0 hB




noncomputable def frameConstant256 (n q : ℕ) (B : ℝ) : ℝ :=
  exactRadius (n - 1 - 1) 128 ^ 2 * (2 / (n : ℝ) * B) *
    ((mA n : ℝ) ^ (1 / (128 * (q : ℝ))) * ((n - 1 - 1 : ℕ) + 256 * (q : ℝ)))

lemma frameConstant256_pow {n q : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q) (B : ℝ) :
    frameConstant256 n q B ^ 128 =
      radialProduct (n - 1 - 1) 128 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 128 *
        (2 / (n : ℝ) * B) ^ 128 *
        ((mA n : ℝ) ^ (1 / (q : ℝ)) * ((n - 1 - 1 : ℕ) + 256 * (q : ℝ)) ^ 128) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hr : (exactRadius (n - 1 - 1) 128 ^ 2) ^ 128 =
      radialProduct (n - 1 - 1) 128 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 128 := by
    rw [← pow_mul]
    exact exactRadius_pow (by omega) (by norm_num)
  have hm : ((mA n : ℝ) ^ (1 / (128 * (q : ℝ)))) ^ (128 : ℕ) =
      (mA n : ℝ) ^ (1 / (q : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    field_simp
  unfold frameConstant256
  simp only [mul_pow]
  rw [hr, hm]

lemma frameConstant256_nonneg {n q : ℕ} {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ frameConstant256 n q B := by
  unfold frameConstant256
  positivity

#print axioms frame_mom256
#print axioms frameConstant256_pow
end BstLean.Part223
