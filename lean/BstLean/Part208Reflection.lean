import BstLean.Part208AxialGaussian

/-! Part 208: reflection identities for an arbitrary retained centre direction. -/
namespace BstLean.Part208
open Real Matrix
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part53 (unitF53)
open BstLean.Part161 (hhMat hh_symm hh_dot hh_normSq hh_mul_transpose hh_e0)

lemma hh_transpose {n : ℕ} (u : Fin n → ℝ) : (hhMat u)ᵀ = hhMat u := by
  ext i j
  exact hh_symm u j i

lemma hh_involutive {n : ℕ} (u ξ : Fin n → ℝ) : hhMat u *ᵥ (hhMat u *ᵥ ξ) = ξ := by
  have hH := hh_mul_transpose u
  rw [hh_transpose] at hH
  calc
    _ = (hhMat u * hhMat u) *ᵥ ξ := by rw [mulVec_mulVec]
    _ = ξ := by rw [hH, one_mulVec]

lemma hh_unitF {n : ℕ} (u ξ : Fin n → ℝ) :
    unitF53 (hhMat u *ᵥ ξ) = hhMat u *ᵥ unitF53 ξ := by
  change (1 / √(normSq (hhMat u *ᵥ ξ))) • (hhMat u *ᵥ ξ) =
    hhMat u *ᵥ ((1 / √(normSq ξ)) • ξ)
  rw [hh_normSq, mulVec_smul]

lemma hh_dot_right {n : ℕ} (u x f : Fin n → ℝ) :
    (hhMat u *ᵥ x) ⬝ᵥ f = x ⬝ᵥ (hhMat u *ᵥ f) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hh_transpose, dotProduct_comm]

lemma hh_zero_coordinate {d : ℕ} {u : Fin (d + 1) → ℝ} (hu : normSq u = 1)
    (f : Fin (d + 1) → ℝ) : (hhMat u *ᵥ f) 0 = u ⬝ᵥ f := by
  have h := hh_dot_right u (BstLean.Part130.e0 (d + 1)) f
  rw [hh_e0 (by omega) hu] at h
  have he := BstLean.Part161.e0_dot (n := d + 1) (by omega) (hhMat u *ᵥ f)
  change BstLean.Part130.e0 (d + 1) ⬝ᵥ (hhMat u *ᵥ f) = (hhMat u *ᵥ f) 0 at he
  exact he.symm.trans h.symm

lemma hh_tail_normSq_le {d : ℕ} (u f : Fin (d + 1) → ℝ) :
    normSq (Fin.tail (hhMat u *ᵥ f)) ≤ normSq f := by
  have h := normSq_cons ((hhMat u *ᵥ f) 0) (Fin.tail (hhMat u *ᵥ f))
  rw [Fin.cons_self_tail, hh_normSq] at h
  nlinarith [sq_nonneg ((hhMat u *ᵥ f) 0)]

lemma hh_shift {d : ℕ} {u : Fin (d + 1) → ℝ} (hu : normSq u = 1)
    (a τ : ℝ) (ξ : Fin (d + 1) → ℝ) :
    hhMat u *ᵥ (Fin.cons a (0 : Fin d → ℝ) + τ • ξ) = a • u + τ • (hhMat u *ᵥ ξ) := by
  have he : Fin.cons a (0 : Fin d → ℝ) = a • BstLean.Part130.e0 (d + 1) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [BstLean.Part130.e0]
  rw [he, mulVec_add, mulVec_smul, mulVec_smul, hh_e0 (by omega) hu]

end BstLean.Part208
