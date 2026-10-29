import BstLean.Part56Defs
import BstLean.Part56Orth_Residual

/-! The residual kernel is a Gram kernel, including zero block norms. -/
namespace BstLean.Part56

open BstLean.Part41 (Mono)

variable {n d : ℕ}

private noncomputable def residualBlock (j : ℕ) (v x : Fin n → ℝ) (p : Mono n d) : ℝ :=
  phiB d j x p - betaJ d j v x * phiB d j v p

private lemma kJ_self_nonneg (j : ℕ) (x : Fin n → ℝ) : 0 ≤ kJ d j x x := by
  unfold kJ
  exact Finset.sum_nonneg (fun p _ => mul_self_nonneg _)

private lemma kJ_symm (j : ℕ) (x y : Fin n → ℝ) : kJ d j x y = kJ d j y x := by
  unfold kJ
  simp only [mul_comm]

private lemma kJ_zero_right (j : ℕ) (v x : Fin n → ℝ) (h : kJ d j v v = 0) :
    kJ d j x v = 0 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (phiB d j x) (phiB d j v)
  have hs (y : Fin n → ℝ) : (∑ p : Mono n d, phiB d j y p ^ 2) = kJ d j y y := by
    simp only [kJ, pow_two]
  change kJ d j x v ^ 2 ≤ _ at hc
  rw [hs x, hs v, h, mul_zero] at hc
  nlinarith [sq_nonneg (kJ d j x v)]

private lemma block_gram (j : ℕ) (v x y : Fin n → ℝ) :
    (∑ p : Mono n d, residualBlock j v x p * residualBlock j v y p) =
      kJ d j x y - kJ d j x v * kJ d j y v / kJ d j v v := by
  classical
  have hterm (p : Mono n d) :
      residualBlock j v x p * residualBlock j v y p =
        phiB d j x p * phiB d j y p -
        betaJ d j v y * (phiB d j x p * phiB d j v p) -
        betaJ d j v x * (phiB d j y p * phiB d j v p) +
        (betaJ d j v x * betaJ d j v y) * (phiB d j v p * phiB d j v p) := by
    unfold residualBlock
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  change kJ d j x y - betaJ d j v y * kJ d j x v -
    betaJ d j v x * kJ d j y v +
    (betaJ d j v x * betaJ d j v y) * kJ d j v v = _
  unfold betaJ
  by_cases h : kJ d j v v = 0
  · simp [h]
  · field_simp
    ring

private noncomputable def residualSet (d : ℕ) : Finset (ℕ × Mono n d) :=
  (Finset.Icc 1 d) ×ˢ (Finset.univ : Finset (Mono n d))

private lemma KR_gram (v x y : Fin n → ℝ) :
    KR d v x y = ∑ q ∈ residualSet (n := n) d,
      residualBlock q.1 v x q.2 * residualBlock q.1 v y q.2 := by
  classical
  unfold residualSet
  rw [Finset.sum_product (Finset.Icc 1 d) (Finset.univ : Finset (Mono n d))
    (fun q => residualBlock q.1 v x q.2 * residualBlock q.1 v y q.2)]
  unfold KR
  apply Finset.sum_congr rfl
  intro j hj
  exact (block_gram j v x y).symm

/-- Nonnegativity of every residual marginal variance. -/
theorem rkg56_tau_nonneg (v x : Fin n → ℝ) : 0 ≤ tauR d v x := by
  rw [tauR, KR_gram]
  exact Finset.sum_nonneg (fun q _ => mul_self_nonneg _)

/-- Cauchy–Schwarz for the residual Gram kernel. -/
theorem rkg56_KR_sq_le (v x y : Fin n → ℝ) :
    KR d v x y ^ 2 ≤ tauR d v x * tauR d v y := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (residualSet (n := n) d)
    (fun q => residualBlock q.1 v x q.2) (fun q => residualBlock q.1 v y q.2)
  simpa only [pow_two, ← KR_gram, tauR] using hc

/-- Every normalized residual correlation lies in `[-1, 1]`. -/
theorem rkg56_abs_rho_le_one (v x y : Fin n → ℝ) : |rhoR d v x y| ≤ 1 := by
  have hK := rkg56_KR_sq_le (d := d) v x y
  have hbound : |KR d v x y| ≤ Real.sqrt (tauR d v x * tauR d v y) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [sq_abs] using hK
  unfold rhoR
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  by_cases hzero : Real.sqrt (tauR d v x * tauR d v y) = 0
  · simp [hzero]
  · exact (div_le_one (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hzero))).mpr hbound

/-- The residual feature's off-diagonal Gram entry is the frozen residual kernel. -/
theorem rkg56_residual_cross (v : Fin n → ℝ) (hv : UnitV v) (x y : Fin n → ℝ) :
    (∑ p : Mono n d, Orth.residualFeature v x p * Orth.residualFeature v y p) = KR d v x y := by
  classical
  have hr (z : Fin n → ℝ) (p : Mono n d) :
      Orth.residualFeature v z p = residualBlock (p.1 : ℕ) v z p := by
    unfold Orth.residualFeature residualBlock
    rw [Finset.sum_eq_single (p.1 : ℕ)]
    · simp [phiB]
    · intro j hj h
      simp [phiB, Ne.symm h]
    · intro h
      exact (h (Finset.mem_range.mpr p.1.2)).elim
  have hp (p : Mono n d) :
      (∑ j ∈ Finset.range (d + 1), residualBlock j v x p * residualBlock j v y p) =
        Orth.residualFeature v x p * Orth.residualFeature v y p := by
    rw [hr x p, hr y p]
    apply Finset.sum_eq_single (p.1 : ℕ)
    · intro j hj h
      simp [residualBlock, phiB, Ne.symm h]
    · intro h
      exact (h (Finset.mem_range.mpr p.1.2)).elim
  simp_rw [← hp]
  rw [Finset.sum_comm]
  simp_rw [block_gram]
  have hz (z : Fin n → ℝ) : phiB d 0 z = phiB d 0 v := by
    funext p
    unfold phiB
    split_ifs with h
    · have hs : (p.2 : Multiset (Fin n)) = 0 :=
        Multiset.card_eq_zero.mp (p.2.2.trans h)
      simp [BstLean.Part41.phiM, BstLean.Part36.monoVal, hs]
    · rfl
  have h0 : kJ d 0 x y - kJ d 0 x v * kJ d 0 y v / kJ d 0 v v = 0 := by
    have hxy : kJ d 0 x y = kJ d 0 v v := by unfold kJ; rw [hz x, hz y]
    have hxv : kJ d 0 x v = kJ d 0 v v := by unfold kJ; rw [hz x]
    have hyv : kJ d 0 y v = kJ d 0 v v := by unfold kJ; rw [hz y]
    rw [hxy, hxv, hyv, mul_div_cancel_right₀ _
      (ne_of_gt (Orth.block_norm_pos v hv 0 (Nat.zero_le _))), sub_self]
  have hi : Finset.range (d + 1) = insert 0 (Finset.Icc 1 d) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hi, Finset.sum_insert (by simp), h0, zero_add]
  rfl

/-- The unnormalized covariance equals correlation times the marginal scales,
including a vanishing marginal scale. -/
theorem rkg56_KR_normalization (v x y : Fin n → ℝ) :
    KR d v x y = Real.sqrt (tauR d v x) * Real.sqrt (tauR d v y) * rhoR d v x y := by
  have hs := Real.sqrt_mul (rkg56_tau_nonneg (d := d) v x) (tauR d v y)
  rw [← hs]
  by_cases hz : Real.sqrt (tauR d v x * tauR d v y) = 0
  · have hp := Real.sq_sqrt
      (mul_nonneg (rkg56_tau_nonneg (d := d) v x) (rkg56_tau_nonneg (d := d) v y))
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at hp
    have hK := rkg56_KR_sq_le (d := d) v x y
    rw [← hp] at hK
    have h0 : KR d v x y = 0 := by nlinarith [sq_nonneg (KR d v x y)]
    simp [hz, h0]
  · unfold rhoR
    exact (mul_div_cancel₀ _ hz).symm

end BstLean.Part56
