import BstLean.Part194MFConc
import BstLean.Part153Cr
import BstLean.Part154App

/-! Supply both norm Lipschitz bounds from the paper's vector Lipschitz hypothesis. -/
namespace BstLean.Part194
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq)
open BstLean.Part148 (EuLip)
open BstLean.Part153 (nrm)
open BstLean.Part154

theorem norm_lipschitz {d m : ℕ} {f : (Fin d → ℝ) → Fin m → ℝ} {L : ℝ}
    (hV : ∀ x y, nrm (f x - f y) ≤ L * nrm (x - y)) :
    EuLip (fun x => nrm (f x)) L := by
  intro x y
  exact (BstLean.Part153.abs_nrm_sub_le _ _).trans (hV x y)

theorem projected_norm_lipschitz {d m : ℕ} {f : (Fin d → ℝ) → Fin m → ℝ}
    {L pg : ℝ} (H : MFHyp (stdGauss (Fin d)) f L pg)
    (hV : ∀ x y, nrm (f x - f y) ≤ L * nrm (x - y)) :
    EuLip (fun x => √(sig2F (stdGauss (Fin d)) f x)) L := by
  intro x y
  have he : gF (stdGauss (Fin d)) f x - gF (stdGauss (Fin d)) f y =
      BstLean.Part153.projB_cr (fbar (stdGauss (Fin d)) f) (f x - f y) := by
    unfold gF BstLean.Part153.projB_cr betaF GamBarF
    rw [sub_dotProduct, sub_div, sub_smul]
    abel
  have hp : nrm (gF (stdGauss (Fin d)) f x - gF (stdGauss (Fin d)) f y) ≤
      nrm (f x - f y) := by
    rw [he]
    exact sqrt_le_sqrt (BstLean.Part153.normSq_projB_le_cr H.hbar.ne' _)
  exact ((BstLean.Part153.abs_nrm_sub_le _ _).trans hp).trans (hV x y)

/-- Both displayed tail supplies hold for a single fixed mean-field input distribution. -/
theorem MF_tail_supply {d m : ℕ} {f : (Fin d → ℝ) → Fin m → ℝ}
    {L pg r rG k k3 : ℝ} (H : MFHyp (stdGauss (Fin d)) f L pg)
    (hV : ∀ x y, nrm (f x - f y) ≤ L * nrm (x - y))
    (hr : 0 < r) (hrG : 0 < rG) (hk : 1 < k) (hk3 : 1 < k3)
    (hRatio : L ^ 2 / sF2 (stdGauss (Fin d)) f ≤ r)
    (hRatioG : L ^ 2 / GamF (stdGauss (Fin d)) f ≤ rG)
    (hRad : 0 ≤ 1 - 2 * r) (hRadG : 0 ≤ 1 - rG)
    (hgap : 0 < gap 2 r k) (hgapG : 0 < gap 1 rG k3) :
    (stdGauss (Fin d)).real {x | sig2F (stdGauss (Fin d)) f x <
      sF2 (stdGauss (Fin d)) f / k} ≤ tail 2 r k ∧
    (stdGauss (Fin d)).real {x | normSq (f x) <
      GamF (stdGauss (Fin d)) f / k3} ≤ tail 1 rG k3 :=
  ⟨MF_sigma_tail H (projected_norm_lipschitz H hV) hr (by linarith)
      hRatio hRad hgap,
    MF_norm_tail H (norm_lipschitz hV) hrG (by linarith) hRatioG hRadG hgapG⟩

/-- The first-layer map has the required vector Lipschitz bound for every fixed matrix. -/
theorem fA_vector_lipschitz {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) {τ L : ℝ}
    (hop : √(2 / (m : ℝ)) * (|τ| * BstLean.Part152.opN A) ≤ L) :
    ∀ x y, nrm (fA A c τ x - fA A c τ y) ≤ L * nrm (x - y) := by
  intro x y
  have e1 : fA A c τ x - fA A c τ y =
      √(2 / (m : ℝ)) • (BstLean.Part130.reluV (A *ᵥ (c + τ • x)) -
        BstLean.Part130.reluV (A *ᵥ (c + τ • y))) := by
    simp only [fA]; rw [smul_sub]
  have e2 : A *ᵥ (c + τ • x) - A *ᵥ (c + τ • y) = A *ᵥ (τ • (x - y)) := by
    rw [← Matrix.mulVec_sub]
    congr 1
    rw [smul_sub]
    abel
  calc nrm (fA A c τ x - fA A c τ y)
      = √(2 / (m : ℝ)) * nrm (BstLean.Part130.reluV (A *ᵥ (c + τ • x)) -
        BstLean.Part130.reluV (A *ᵥ (c + τ • y))) := by
          rw [e1, BstLean.Part153.nrm_smul, abs_of_nonneg (sqrt_nonneg _)]
    _ ≤ √(2 / (m : ℝ)) * nrm (A *ᵥ (c + τ • x) - A *ᵥ (c + τ • y)) :=
      mul_le_mul_of_nonneg_left (BstLean.Part153.nrm_reluV_sub_le _ _) (sqrt_nonneg _)
    _ = √(2 / (m : ℝ)) * nrm (A *ᵥ (τ • (x - y))) := by rw [e2]
    _ ≤ √(2 / (m : ℝ)) * (BstLean.Part152.opN A * nrm (τ • (x - y))) :=
      mul_le_mul_of_nonneg_left (BstLean.Part153.nrm_mulVec_le _ _) (sqrt_nonneg _)
    _ = √(2 / (m : ℝ)) * (|τ| * BstLean.Part152.opN A) * nrm (x - y) := by
      rw [BstLean.Part153.nrm_smul]; ring
    _ ≤ L * nrm (x - y) :=
      mul_le_mul_of_nonneg_right hop (BstLean.Part153.nrm_nonneg _)

#print axioms fA_vector_lipschitz
#print axioms norm_lipschitz
#print axioms projected_norm_lipschitz
#print axioms MF_tail_supply
end BstLean.Part194
