import BstLean.Part56Low_Conditional
import BstLean.Part56Low_Scale
import BstLean.Part56Low_Coefficients
import BstLean.Part43Floor

namespace BstLean.Part56.LowPointwise

open MeasureTheory BstLean.Part29 BstLean.Part36 BstLean.Part41 BstLean.Part53
open LowConditional LowFeature LowScale LowCoefficients

variable {n d : ℕ}

lemma perpendicular_sq_nonneg (v x : Fin n → ℝ) (hv : UnitV v) (hx : UnitV x) :
    0 ≤ 1 - (∑ a, x a * v a) ^ 2 := by
  classical
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x v
  change (∑ a, x a * v a) ^ 2 ≤ (∑ a, x a ^ 2) * ∑ a, v a ^ 2 at hs
  have hx' : (∑ a, x a ^ 2) = 1 := hx
  have hv' : (∑ a, v a ^ 2) = 1 := hv
  rw [hx', hv', one_mul] at hs
  linarith

lemma cvar_norm_lower (k : ℕ) (hd : 1 ≤ d) (f0 : ℝ) (T : Tens n)
    (hT : TSymm k T) (s : ℝ) (hs : 0 ≤ s) (v x : Fin n → ℝ)
    (hv : UnitV v) (hx : UnitV x) :
    (1 - (∑ a, x a * v a) ^ 2) ^ k *
      normSum k (heatA k (phiSq d x) (scaleT s (TF k f0 T))) ≤
      ∫ Z, cvarG k f0 T (s * Real.sqrt (tauR d v x)) (mux (s • Z) v x)
        ∂stdGauss (CoefIdxD n d) := by
  classical
  let A := TF k f0 T
  let B := heatA k (phiSq d x) (scaleT s A)
  let r := (1 - (∑ a, x a * v a) ^ 2) ^ k
  have hr0 : 0 ≤ r := pow_nonneg (perpendicular_sq_nonneg v x hv hx) k
  rw [cvar_energy_integral k f0 T hT s hs v hv x]
  have hrange : Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) := by
    ext c
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hrange, Finset.sum_insert (by simp)]
  simp only [pow_zero, sub_self, mul_zero, zero_add]
  unfold normSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  have hc' := Finset.mem_Icc.mp hc
  have hp : r ≤ phiSq d x ^ c - nsq (anchorFeature (d := d) v x) ^ c :=
    (residual_power_lower56 d k c hd hc'.2 v x hv hx).trans
      (residual_power_difference c hc'.1 v hv x)
  have hp0 := hr0.trans hp
  have hfac : (1 : ℝ) ≤ c.factorial := by exact_mod_cast Nat.factorial_pos c
  have hb0 : 0 ≤ frob (B c) := Finset.sum_nonneg fun w _ => sq_nonneg _
  change r * frob (B c) ≤ _
  calc
    _ ≤ frob (B c) * (phiSq d x ^ c - nsq (anchorFeature (d := d) v x) ^ c) := by
      simpa only [mul_comm r] using mul_le_mul_of_nonneg_left hp hb0
    _ ≤ (c.factorial : ℝ) * (frob (B c) *
        (phiSq d x ^ c - nsq (anchorFeature (d := d) v x) ^ c)) :=
      le_mul_of_one_le_left (mul_nonneg hb0 hp0) hfac
    _ = _ := by
      dsimp [B, A]
      rw [heated_frob_scaled]
      ring

lemma pointwise_coefficient_lower (k : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (f0 : ℝ) (T : Tens n) (hT : TSymm k T) (s : ℝ) (hs : 0 ≤ s)
    (v x : Fin n → ℝ) (hv : UnitV v) (hx : UnitV x) :
    (1 - (∑ a, x a * v a) ^ 2) ^ k * normSum k (scaleT s (TF k f0 T)) ≤
      ((k + 1 : ℝ) ^ 3 * weightBound d k) * (n : ℝ) ^ ((k - 1) / 2) *
      ∫ Z, cvarG k f0 T (s * Real.sqrt (tauR d v x)) (mux (s • Z) v x)
        ∂stdGauss (CoefIdxD n d) := by
  have hbounds := BstLean.Part43.phiSq_bounds hd x hx
  have hi := inverse_normSum_bound d k hn (phiSq d x) (by linarith) hbounds.2
    (scaleT s (TF k f0 T))
  have hl := cvar_norm_lower k hd f0 T hT s hs v x hv hx
  have hr0 : 0 ≤ (1 - (∑ a, x a * v a) ^ 2) ^ k :=
    pow_nonneg (perpendicular_sq_nonneg v x hv hx) k
  have hW := (weightBound_pos d k).le
  have hC : 0 ≤ ((k + 1 : ℝ) ^ 3 * weightBound d k) * (n : ℝ) ^ ((k - 1) / 2) := by positivity
  calc
    _ ≤ (1 - (∑ a, x a * v a) ^ 2) ^ k *
        ((k + 1 : ℝ) ^ 3 * weightBound d k * (n : ℝ) ^ ((k - 1) / 2) *
          normSum k (heatA k (phiSq d x) (scaleT s (TF k f0 T)))) :=
      mul_le_mul_of_nonneg_left hi hr0
    _ = (((k + 1 : ℝ) ^ 3 * weightBound d k) * (n : ℝ) ^ ((k - 1) / 2)) *
        ((1 - (∑ a, x a * v a) ^ 2) ^ k *
          normSum k (heatA k (phiSq d x) (scaleT s (TF k f0 T)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl hC


end BstLean.Part56.LowPointwise
