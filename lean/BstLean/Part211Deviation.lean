import BstLean.Part211Source
import BstLean.Part206Sharp

/-! The sharp MA deviation in the paper's retained-data normalization. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC gO sO2)
open BstLean.Part153 (wn)
open BstLean.Part154 (GamBarF fA GamBarF_fA)

noncomputable def sharpDeviation (n : ℕ) (cs δe θlo Θ : ℝ) : ℝ :=
  √24 * (√(2 * (1 + δe - cs * θlo / 2) / n) + 2 * √(wn n * Θ) / n)

/-- Source energy and noise bounds supply the normalized sharp concentration deviation. -/
theorem MA_normalized_deviation {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ)
    {τ cs δe θlo Θ L : ℝ} (hτ : 0 < τ) (hcs : 0 ≤ cs)
    (hlo : θlo ≤ thetaC c τ) (hhi : thetaC c τ ≤ Θ)
    (hsc : cs * τ ^ 2 ≤ sO2 A c τ)
    (hEe : gO A c τ ≤ (1 + δe) * (2 / n) * rhoC c τ ^ 2)
    (hL : L ^ 2 ≤ 4 * wn n * τ ^ 2 / n) :
    √(24 * (2 / (mA n : ℝ))) *
        (√(GamBarF (stdGauss (Fin n)) (fA A c τ)) + L) /
        (rhoC c τ * √(2 / (n : ℝ) / n)) ≤ sharpDeviation n cs δe θlo Θ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn c hτ
  have hθ := (BstLean.Part150.thetaC_bounds hn c hτ).1
  have hΘ : 0 < Θ := hθ.trans_le hhi
  have hw : 0 < wn n := by unfold wn; positivity
  have ht : τ ^ 2 = rhoC c τ ^ 2 * thetaC c τ / n := by
    unfold thetaC
    field_simp
  have hb : GamBarF (stdGauss (Fin n)) (fA A c τ) = gO A c τ - sO2 A c τ := by
    rw [GamBarF_fA]
    unfold sO2 normSq
    ring
  let v := 2 * (1 + δe - cs * θlo / 2) / (n : ℝ)
  have hbar : GamBarF (stdGauss (Fin n)) (fA A c τ) ≤ rhoC c τ ^ 2 * v := by
    have hnoise := mul_le_mul_of_nonneg_left hlo hcs
    have hnoise' := mul_le_mul_of_nonneg_left hnoise
      (show 0 ≤ rhoC c τ ^ 2 / n by positivity)
    rw [ht] at hsc
    rw [hb]
    dsimp [v]
    ring_nf at hEe hsc hnoise' ⊢
    linarith only [hEe, hsc, hnoise']
  have hbar0 : 0 ≤ GamBarF (stdGauss (Fin n)) (fA A c τ) := normSq_nonneg _
  have hv : 0 ≤ v := by nlinarith [sq_pos_of_pos hρ]
  have hroot : √(GamBarF (stdGauss (Fin n)) (fA A c τ)) / rhoC c τ ≤ √v := by
    have h := sqrt_le_sqrt hbar
    rw [sqrt_mul (sq_nonneg _), sqrt_sq hρ.le] at h
    exact (div_le_iff₀ hρ).mpr (by nlinarith only [h])
  have hL2 : L ^ 2 ≤ (rhoC c τ * (2 * √(wn n * Θ) / n)) ^ 2 := by
    have hc := mul_le_mul_of_nonneg_left hhi
      (show 0 ≤ 4 * wn n * rhoC c τ ^ 2 / (n : ℝ) ^ 2 by positivity)
    rw [ht] at hL
    rw [mul_pow, div_pow, mul_pow, sq_sqrt (mul_nonneg hw.le hΘ.le)]
    convert hL.trans (by convert hc using 1 <;> ring) using 1 <;> ring
  have hLroot : L / rhoC c τ ≤ 2 * √(wn n * Θ) / n := by
    rw [div_le_iff₀ hρ]
    have hp : 0 ≤ rhoC c τ * (2 * √(wn n * Θ) / n) := by positivity
    nlinarith only [hL2, hp]
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have he : √(24 * (2 / (mA n : ℝ))) = √24 * √(2 / (n : ℝ) / n) := by
    rw [hm, sqrt_mul (by norm_num)]
    congr 1
    congr 1
    ring
  rw [he]
  have hs : 0 < √(2 / (n : ℝ) / n) := by positivity
  have he2 : √24 * √(2 / (n : ℝ) / n) *
      (√(GamBarF (stdGauss (Fin n)) (fA A c τ)) + L) /
      (rhoC c τ * √(2 / (n : ℝ) / n)) =
      √24 * (√(GamBarF (stdGauss (Fin n)) (fA A c τ)) / rhoC c τ + L / rhoC c τ) := by
    field_simp
  rw [he2]
  exact mul_le_mul_of_nonneg_left (add_le_add hroot hLroot) (sqrt_nonneg _)

def SharpMA (n : ℕ) (c : Fin n → ℝ) (τ : ℝ)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) :
    Set (Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  {M | BstLean.Part154.dC A M c τ ≤
    (∫ M, BstLean.Part154.dC A M c τ ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) +
    √(24 * (2 / (mA n : ℝ))) *
      (√(GamBarF (stdGauss (Fin n)) (fA A c τ)) + √(4 * wn n * τ ^ 2 / n))}

/-- The operator and variance source events discharge the sharp Lipschitz hypothesis. -/
theorem sharp_MA_source_charge {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ)
    {τ cs : ℝ} (hτ : 0 < τ) (hcs : 0 < cs)
    (hr : BstLean.Part154.rhoBar n cs < 1 / 4)
    (hop : A ∈ BstLean.Part153.Eop n) (hsc : cs * τ ^ 2 ≤ sO2 A c τ) :
    (gaussMat (mA n) (mA n) (2 / (mA n : ℝ))).real (SharpMA n c τ A)ᶜ ≤ exp (-12) := by
  obtain ⟨L, r, hL, _, _, _, H, _⟩ := BstLean.Part160.setupMA_I hn A c hτ hcs hr
    (BstLean.Part153.Eop_sq hn hop) hsc
  have hLe : L = √(4 * wn n * τ ^ 2 / n) := by
    rw [← hL, sqrt_sq H.hℓ.le]
  have h := BstLean.Part206.MA_actual_sharp_charge (one_le_mA hn) A c τ H
    (level := 12) (by norm_num)
  rw [hLe] at h
  simpa only [SharpMA, compl_setOf, not_le, show (2 : ℝ) * 12 = 24 by norm_num] using h

/-- The same sharp source event supplies the normalized MA amplitude in every valid cell. -/
theorem MA_on_sharp_source {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ)
    {τ cs δe θlo Θ ξ : ℝ} (hτ : 0 < τ) (hcs : 0 ≤ cs)
    (hlo : θlo ≤ thetaC c τ) (hhi : thetaC c τ ≤ Θ) (hξ : 0 ≤ ξ)
    (hsc : cs * τ ^ 2 ≤ sO2 A c τ)
    (hEe : gO A c τ ≤ (1 + δe) * (2 / n) * rhoC c τ ^ 2)
    (hMoment : (∫ M, BstLean.Part154.dC A M c τ ^ 2
      ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) ≤
        rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * ξ)
    {M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} (hM : M ∈ SharpMA n c τ A) :
    BstLean.Part154.dC A M c τ ≤
      rhoC c τ * √(2 / (n : ℝ) / n) * (√ξ + sharpDeviation n cs δe θlo Θ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn c hτ
  have hw : 0 < wn n := by unfold wn; positivity
  have hd := MA_normalized_deviation hn A c hτ hcs hlo hhi hsc hEe
    (L := √(4 * wn n * τ ^ 2 / n)) (by rw [sq_sqrt (by positivity)])
  rw [div_le_iff₀ (by positivity : 0 < rhoC c τ * √(2 / (n : ℝ) / n))] at hd
  obtain ⟨hi, hi2⟩ := BstLean.Part154.dC_integrable (one_le_mA hn) A c τ
  apply BstLean.Part206.MA_mean_threshold (by positivity) hξ hi hi2
  · simpa only [mul_pow, sq_sqrt (by positivity : 0 ≤ 2 / (n : ℝ) / n)] using hMoment
  · simp only [SharpMA, mem_setOf_eq] at hM
    nlinarith only [hM, hd]

#print axioms sharp_MA_source_charge
#print axioms MA_on_sharp_source
#print axioms MA_normalized_deviation
end BstLean.Part211
