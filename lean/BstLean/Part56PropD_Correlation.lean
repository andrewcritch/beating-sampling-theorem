import BstLean.Part56PropD_Bounds
import BstLean.Part56PropD_Moments

/-! Pointwise residual correlation estimate on the polar decomposition. -/
namespace BstLean.Part56

open MeasureTheory
open BstLean.Part41 (Mono)

variable {n : ℕ}

theorem tauR_ge_first (d : ℕ) (hd : 1 ≤ d) (v x : Fin n → ℝ) (hv : UnitV v) :
    (∑ i, x i ^ 2) - (∑ i, x i * v i) ^ 2 ≤ tauR d v x := by
  classical
  have hmem : 1 ∈ Finset.Icc 1 d := by simp [hd]
  have hle := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.Icc 1 d) =>
      Finset.sum_nonneg fun p (_ : p ∈ Finset.univ) =>
        mul_self_nonneg (residualB d j v x p)) hmem
  rw [← KR_gram, residualB_gram, kJ_one d hd, kJ_one d hd, kJ_one d hd] at hle
  change ∑ i, v i ^ 2 = 1 at hv
  simpa only [← pow_two, hv, div_one, tauR] using hle

theorem tauR_polar_ge (d : ℕ) (hd : 1 ≤ d) (v w : Fin n → ℝ)
    (hv : UnitV v) (hw : UnitV w) (hvw : (∑ i, v i * w i) = 0) (s r : ℝ) :
    r ^ 2 ≤ tauR d v (s • v + r • w) := by
  have hdot : (∑ i, (s • v + r • w) i * v i) = s := by
    have he (i : Fin n) : (s • v + r • w) i * v i =
        s * v i ^ 2 + r * (v i * w i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hv, hvw]
    ring
  have hnorm : (∑ i, (s • v + r • w) i ^ 2) = s ^ 2 + r ^ 2 := by
    have he (i : Fin n) : (s • v + r • w) i ^ 2 =
        s ^ 2 * v i ^ 2 + (2 * s * r) * (v i * w i) + r ^ 2 * w i ^ 2 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, hv, hw, hvw]
    ring
  have h := tauR_ge_first d hd v (s • v + r • w) hv
  rw [hdot, hnorm] at h
  linarith

theorem KR_polar (d : ℕ) (v w w' : Fin n → ℝ) (s r s' r' : ℝ) :
    KR d v (s • v + r • w) (s' • v + r' • w') =
      (r * r') * ∑ j ∈ Finset.Icc 1 d, ∑ p : Mono n d,
        projectOff (phiB d j v) (psiHat d j s r v w) p *
          projectOff (phiB d j v) (psiHat d j s' r' v w') p := by
  classical
  rw [KR_gram, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [residualB_polar, Pi.smul_apply, smul_eq_mul]
  ring

theorem rhoR_polar_sq_le (d : ℕ) (hd : 1 ≤ d) (v w w' : Fin n → ℝ)
    (hv : UnitV v) (hw : UnitV w) (hw' : UnitV w')
    (hvw : (∑ i, v i * w i) = 0) (hvw' : (∑ i, v i * w' i) = 0)
    (s r s' r' : ℝ) :
    rhoR d v (s • v + r • w) (s' • v + r' • w') ^ 2 ≤
      (d : ℝ) * ∑ j ∈ Finset.Icc 1 d,
        (∑ p : Mono n d, projectOff (phiB d j v) (psiHat d j s r v w) p *
          projectOff (phiB d j v) (psiHat d j s' r' v w') p) ^ 2 := by
  classical
  let x := s • v + r • w
  let y := s' • v + r' • w'
  let Q (j : ℕ) := ∑ p : Mono n d,
    projectOff (phiB d j v) (psiHat d j s r v w) p *
      projectOff (phiB d j v) (psiHat d j s' r' v w') p
  have hC : 0 ≤ (d : ℝ) * ∑ j ∈ Finset.Icc 1 d, Q j ^ 2 := by positivity
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 d) (fun _ => (1 : ℝ)) Q
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    Nat.card_Icc, Nat.add_sub_cancel, Nat.sub_zero] at hc
  have hx := tauR_polar_ge d hd v w hv hw hvw s r
  have hy := tauR_polar_ge d hd v w' hv hw' hvw' s' r'
  have ht : r ^ 2 * r' ^ 2 ≤ tauR d v x * tauR d v y :=
    mul_le_mul hx hy (sq_nonneg _) (tauR_nonneg d v x)
  have hk : KR d v x y ^ 2 ≤ (tauR d v x * tauR d v y) *
      ((d : ℝ) * ∑ j ∈ Finset.Icc 1 d, Q j ^ 2) := by
    rw [KR_polar]
    change ((r * r') * ∑ j ∈ Finset.Icc 1 d, Q j) ^ 2 ≤ _
    calc
      _ = (r ^ 2 * r' ^ 2) * (∑ j ∈ Finset.Icc 1 d, Q j) ^ 2 := by ring
      _ ≤ (r ^ 2 * r' ^ 2) * ((d : ℝ) * ∑ j ∈ Finset.Icc 1 d, Q j ^ 2) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right ht hC
  by_cases hz : Real.sqrt (tauR d v x * tauR d v y) = 0
  · change rhoR d v x y ^ 2 ≤ _
    simp only [rhoR, hz, div_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)]
    exact hC
  · have hp : 0 < Real.sqrt (tauR d v x * tauR d v y) ^ 2 := sq_pos_of_ne_zero hz
    change rhoR d v x y ^ 2 ≤ _
    rw [rhoR, div_pow, div_le_iff₀ hp,
      Real.sq_sqrt (mul_nonneg (tauR_nonneg d v x) (tauR_nonneg d v y))]
    simpa only [mul_comm] using hk

theorem perpDir_unit_or_zero (v g : Fin n → ℝ) :
    UnitV (perpDir v g) ∨ perpDir v g = 0 := by
  let S : ℝ := ∑ i, (g i - (∑ l, v l * g l) * v i) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hz : Real.sqrt S = 0
  · right
    ext i
    simp [perpDir, S, hz]
  · left
    have he : (1 / Real.sqrt S) ^ 2 * S = 1 := by
      field_simp
      exact (Real.sq_sqrt hS).symm
    simp only [UnitV, perpDir, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    exact he

theorem residualB_axis (d j : ℕ) (v : Fin n → ℝ) (s : ℝ) :
    residualB d j v (s • v) = 0 := by
  have h := residualB_polar d j s 0 v 0
  simpa using h

theorem rhoR_axis_left (d : ℕ) (v y : Fin n → ℝ) (s : ℝ) :
    rhoR d v (s • v) y = 0 := by
  simp [rhoR, KR_gram, residualB_axis]

theorem rhoR_axis_right (d : ℕ) (v x : Fin n → ℝ) (s : ℝ) :
    rhoR d v x (s • v) = 0 := by
  simp [rhoR, KR_gram, residualB_axis]

theorem rhoR_polarState_sq_le {k : ℕ} (d : ℕ) (hd : 1 ≤ d)
    (v : Fin (k + 1) → ℝ) (hv : UnitV v)
    (x y : (ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ)) :
    rhoR d v (polarState v x) (polarState v y) ^ 2 ≤
      (d : ℝ) * ∑ j ∈ Finset.Icc 1 d,
        (∑ p : Mono (k + 1) d, projectOff (phiB d j v) (mixedPsi d j v x) p *
          projectOff (phiB d j v) (mixedPsi d j v y) p) ^ 2 := by
  have h0 : 0 ≤ (d : ℝ) * ∑ j ∈ Finset.Icc 1 d,
      (∑ p : Mono (k + 1) d, projectOff (phiB d j v) (mixedPsi d j v x) p *
        projectOff (phiB d j v) (mixedPsi d j v y) p) ^ 2 := by positivity
  rcases perpDir_unit_or_zero v x.2 with hx | hx
  · rcases perpDir_unit_or_zero v y.2 with hy | hy
    · exact rhoR_polar_sq_le d hd v _ _ hv hx hy
        (perpDir_orthogonal v x.2 hv) (perpDir_orthogonal v y.2 hv) _ _ _ _
    · simpa only [polarState, polarPoint, hy, smul_zero, add_zero,
        rhoR_axis_right, zero_pow (by omega : (2 : ℕ) ≠ 0)] using h0
  · simpa only [polarState, polarPoint, hx, smul_zero, add_zero,
      rhoR_axis_left, zero_pow (by omega : (2 : ℕ) ≠ 0)] using h0

end BstLean.Part56
