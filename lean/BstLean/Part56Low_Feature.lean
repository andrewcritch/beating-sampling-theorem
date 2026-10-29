import BstLean.Part56Low_Kernel
import BstLean.Part56Orth_Residual

namespace BstLean.Part56.LowFeature

open BstLean.Part36 BstLean.Part41 BstLean.Part53

variable {n d : ℕ}

noncomputable def anchorFeature (v x : Fin n → ℝ) : Mono n d → ℝ :=
  fun p => ∑ j ∈ Finset.range (d + 1), betaJ d j v x * phiB d j v p

lemma anchor_value (v x : Fin n → ℝ) (Z : CoefIdxD n d → ℝ) :
    linZ Z (anchorFeature v x) = mux Z v x := by
  classical
  funext a
  simp only [linZ, anchorFeature, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mux, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ancRK, linZ]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

private lemma full_block_inner (v x : Fin n → ℝ) (j : ℕ) :
    (∑ p : Mono n d, phiM x p * phiB d j v p) = kJ d j x v := by
  classical
  apply Finset.sum_congr rfl
  intro p hp
  unfold phiB
  split_ifs <;> ring

lemma anchor_inner (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) (j : ℕ)
    (hj : j ≤ d) :
    (∑ p : Mono n d, anchorFeature v x p * phiB d j v p) = kJ d j x v := by
  classical
  simp only [anchorFeature, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [Finset.sum_eq_single j]
  · change betaJ d j v x * kJ d j v v = _
    exact div_mul_cancel₀ _ (ne_of_gt (Orth.block_norm_pos v hv j hj))
  · intro l hl hlj
    rw [Orth.blocks_orthogonal l j v hlj, mul_zero]
  · simp [hj]

lemma residual_anchor_inner (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    (∑ p : Mono n d, Orth.residualFeature v x p * anchorFeature v x p) = 0 := by
  classical
  simp only [anchorFeature, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have hjd : j ≤ d := by have := Finset.mem_range.mp hj; omega
  have he : (∑ p : Mono n d, Orth.residualFeature v x p * phiB d j v p) = 0 := by
    change (∑ p : Mono n d, (phiM x p - anchorFeature v x p) * phiB d j v p) = 0
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [full_block_inner, anchor_inner v hv x j hjd, sub_self]
  calc
    _ = betaJ d j v x * ∑ p : Mono n d, Orth.residualFeature v x p * phiB d j v p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = 0 := by rw [he, mul_zero]

lemma full_norm_split (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    phiSq d x = tauR d v x + nsq (anchorFeature (d := d) v x) := by
  classical
  have he (p : Mono n d) : phiM x p = Orth.residualFeature v x p + anchorFeature v x p := by
    unfold Orth.residualFeature anchorFeature
    ring
  have hsq : phiSq d x = nsq (Orth.residualFeature (d := d) v x) +
      2 * (∑ p : Mono n d, Orth.residualFeature v x p * anchorFeature v x p) +
      nsq (anchorFeature (d := d) v x) := by
    unfold phiSq nsq
    simp_rw [he]
    simp_rw [add_sq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
  rw [Orth.residualFeature_norm v hv x, residual_anchor_inner v hv x] at hsq
  simpa using hsq


end BstLean.Part56.LowFeature
