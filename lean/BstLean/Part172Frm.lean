import BstLean.Part172FNum

/-!
# Part 172 (file `Frm`): the frame moment of a first-layer tangential statistic

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, `t7:p08:LJ1` (with `ℓ = 128`, in Lean's frame form).

* `fr_frame`: in the frame variables, for a direction `e(A₁)` that reads `A₁` only through
  `A₁x`, `A₁u` and the row lengths, with `|e|² ≤ B`:
  `E latSq((D₁A₁)ᵀe)^{64} ≤ K_d (γB)^{64} m^{1/q}(d+128q)^{64}` (Part 168's `polar_core`).
* **`frame_mom`**: the same at the latitude point `x = xLat c s (unitF53 v)`.
* **`frame_mom_num`**: for `|e|² ≤ t_A` and `n ≥ 80 000`, the bound is `(4.25/n²)^{64}`.
-/

namespace BstLean.Part172

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

/-- The frame coefficients `κ_i = √γ e_i mask_i`. -/
noncomputable def fr_kap (hn2 : 2 ≤ n) (u w : Fin n → ℝ) (s cs : ℝ)
    (e : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (W : Fin (mA n) → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ)) : Fin (mA n) → ℝ := fun i =>
  √(2 / (n : ℝ)) * e (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W) i *
    mask ((Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs) W *ᵥ (s • u + cs • w)) i)

theorem fr_frame (hn : 4 ≤ n) {q : ℕ} (hq : 1 ≤ q) {u w : Fin n → ℝ} {s cs : ℝ}
    (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (hsc : s ^ 2 + cs ^ 2 = 1)
    (e : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (hadm : ∀ A A' : Matrix (Fin (mA n)) (Fin n) ℝ, A *ᵥ (s • u + cs • w) = A' *ᵥ (s • u + cs • w) →
      A *ᵥ u = A' *ᵥ u → (∀ i, ∑ j, A i j ^ 2 = ∑ j, A' i j ^ 2) → e A = e A')
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ A, normSq (e A) ≤ B) :
    ∫⁻ A₁, ENNReal.ofReal (latSq (vecMul (e A₁) (D1A1 A₁ (s • u + cs • w))) u w ^ 64)
        ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal ((((n - 1 - 1 : ℕ) : ℝ) + 128) ^ 64 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 64 *
        (2 / (n : ℝ) * B) ^ 64 *
        ((((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / q) * (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) ^ 64))) := by
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
      (eprime hn2 u w s cs) W) (s • u + cs • w))) u w ^ 64) =
      ENNReal.ofReal (normSq (∑ i, fr_kap hn2 u w s cs e W i • (W i).2.2) ^ 64) := by
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
  have hP := BstLean.Part168.polar_core hm0 hd hq (fr_kap hn2 u w s cs e) hinv
    (mul_nonneg hγ hB0) hkB
  refine hP.trans (le_of_eq ?_)
  congr 1


/-- The orthonormal frame `(û, w)` at a direction `v ≠ 0`. -/
lemma fr_orth (hn : 1 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    normSq (uHat c) = 1 ∧ normSq (dirW c (unitF53 v)) = 1 ∧
      ∑ i, uHat c i * dirW c (unitF53 v) i = 0 := by
  refine ⟨BstLean.Part161.normSq_uHat hc, ?_, ?_⟩
  · unfold dirW
    rw [BstLean.Part161.hh_normSq, BstLean.Part161.normSq_consV hn]
    have h1 : normSq (unitF53 v) = radF53 (unitF53 v) ^ 2 := (BstLean.Part162.radF_sq _).symm
    rw [h1, BstLean.Part162.radF_unitF hv]; ring
  · have h := BstLean.Part161.dir_orth hn hc (unitF53 v)
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by unfold dirW; ring

lemma fr_xLat (hn : 1 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) (s : ℝ) (v : Fin (n - 1) → ℝ) :
    xLat c s (unitF53 v) = s • uHat c + √(1 - s ^ 2) • dirW c (unitF53 v) := by
  rw [BstLean.Part161.xLat_eq hn hc]; rfl

/-- **The frame moment of a first-layer tangential statistic** for an admissible direction
`e` with `|e|² ≤ B`: `E_{A₁} latSq((D₁A₁)ᵀe)^{64} ≤ K_d (γB)^{64} m^{1/q}(d+128q)^{64}`. -/
theorem frame_mom (hn : 4 ≤ n) {q : ℕ} (hq : 1 ≤ q) {c : Ret n} (hc : c.1.2 ≠ 0) {s : ℝ}
    (hs : s ^ 2 ≤ 1) {v : Fin (n - 1) → ℝ} (hv : v ≠ 0)
    (e : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (hadm : ∀ A A' : Matrix (Fin (mA n)) (Fin n) ℝ, A *ᵥ xLat c s (unitF53 v) =
      A' *ᵥ xLat c s (unitF53 v) → A *ᵥ uHat c = A' *ᵥ uHat c →
      (∀ i, ∑ j, A i j ^ 2 = ∑ j, A' i j ^ 2) → e A = e A')
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ A, normSq (e A) ≤ B) :
    ∫⁻ A₁, ENNReal.ofReal (latSq (vecMul (e A₁) (D1A1 A₁ (xLat c s (unitF53 v)))) (uHat c)
        (dirW c (unitF53 v)) ^ 64) ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal ((((n - 1 - 1 : ℕ) : ℝ) + 128) ^ 64 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 64 *
        (2 / (n : ℝ) * B) ^ 64 *
        ((((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / q) * (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) ^ 64))) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hu, hw, huw⟩ := fr_orth hn1 hc hv
  have hsc : s ^ 2 + √(1 - s ^ 2) ^ 2 = 1 := by rw [Real.sq_sqrt (by linarith)]; ring
  rw [fr_xLat hn1 hc] at hadm ⊢
  exact fr_frame hn hq hu hw huw hsc e hadm hB0 hB


/-- **The frame moment with the numbers**: for every `n ≥ 80 000` and an admissible direction
with `|e|² ≤ t_A`, `E_{A₁} latSq((D₁A₁)ᵀe)^{64} ≤ (4.25/n²)^{64}`. -/
theorem frame_mom_num (hn : 80000 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) {s : ℝ}
    (hs : s ^ 2 ≤ 1) {v : Fin (n - 1) → ℝ} (hv : v ≠ 0)
    (e : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (hadm : ∀ A A' : Matrix (Fin (mA n)) (Fin n) ℝ, A *ᵥ xLat c s (unitF53 v) =
      A' *ᵥ xLat c s (unitF53 v) → A *ᵥ uHat c = A' *ᵥ uHat c →
      (∀ i, ∑ j, A i j ^ 2 = ∑ j, A' i j ^ 2) → e A = e A')
    (hB : ∀ A, normSq (e A) ≤ BstLean.Part170.tA n) :
    ∫⁻ A₁, ENNReal.ofReal (latSq (vecMul (e A₁) (D1A1 A₁ (xLat c s (unitF53 v)))) (uHat c)
        (dirW c (unitF53 v)) ^ 64) ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal ((425 / 100 / (n : ℝ) ^ 2) ^ 64) := by
  have hq : 1 ≤ BstLean.Part168.qn n := by have := BstLean.Part168.q_ge hn; omega
  have htA : (0 : ℝ) ≤ BstLean.Part170.tA n := BstLean.Part171.tA_nonneg n
  refine (frame_mom (by omega) hq hc hs hv e hadm htA hB).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [fr_X_pow hq]
  have hX0 : 0 ≤ fr_X n (BstLean.Part168.qn n) (BstLean.Part170.tA n) := by
    have hd : (2 : ℝ) ≤ ((n - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
    unfold fr_X
    refine mul_nonneg (mul_nonneg ?_ (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_))
      (mul_nonneg (by positivity) htA)
    · apply div_nonneg <;> linarith
    · positivity
  exact pow_le_pow_left₀ hX0 (fr_X_num hn) 64

end BstLean.Part172
