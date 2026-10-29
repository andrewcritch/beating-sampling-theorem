import BstLean.Part56Defs

namespace BstLean.Part56

open BstLean.Part41

variable {n : ℕ}

lemma propLow56_of_neg (d k : ℕ) (C : ℝ) (hC : C < 0) :
    ∃ (cL : ℝ) (n0 : ℕ), 0 < cL ∧ PropLow56 d k C cL n0 := by
  refine ⟨1, 1, by norm_num, ?_⟩
  intro n hn v hv t ht htC f0 T hT
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hCn : C * n < 0 := mul_neg_of_neg_of_pos hC hnpos
  linarith

lemma kJ_diag_nonneg56 (d j : ℕ) (x : Fin n → ℝ) : 0 ≤ kJ d j x x := by
  classical
  unfold kJ
  exact Finset.sum_nonneg fun p _ => mul_self_nonneg _

lemma kJ_cauchy56 (d j : ℕ) (x v : Fin n → ℝ) :
    kJ d j x v ^ 2 ≤ kJ d j x x * kJ d j v v := by
  classical
  simpa only [kJ, pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (phiB d j x) (phiB d j v)

lemma residual_diag_nonneg56 (d j : ℕ) (v x : Fin n → ℝ) :
    0 ≤ kJ d j x x - kJ d j x v * kJ d j x v / kJ d j v v := by
  have hb := kJ_diag_nonneg56 d j v
  by_cases hz : kJ d j v v = 0
  · simpa [hz] using kJ_diag_nonneg56 d j x
  · have hp : 0 < kJ d j v v := lt_of_le_of_ne hb (Ne.symm hz)
    have hc := kJ_cauchy56 d j x v
    have hdiv : kJ d j x v * kJ d j x v / kJ d j v v ≤ kJ d j x x :=
      (div_le_iff₀ hp).mpr (by simpa [pow_two] using hc)
    linarith

lemma tauR_nonneg56 (d : ℕ) (v x : Fin n → ℝ) : 0 ≤ tauR d v x := by
  classical
  unfold tauR KR
  exact Finset.sum_nonneg fun j _ => residual_diag_nonneg56 d j v x

lemma kJ_one56 (d : ℕ) (hd : 1 ≤ d) (x y : Fin n → ℝ) :
    kJ d 1 x y = ∑ a, x a * y a := by
  classical
  unfold kJ phiB
  rw [Fintype.sum_sigma]
  let one : Fin (d + 1) := ⟨1, by omega⟩
  have hm (i : Fin (d + 1)) :
      (∑ b : Sym (Fin n) i, (if (i : ℕ) = 1 then phiM x ⟨i,b⟩ else 0) *
        (if (i : ℕ) = 1 then phiM y ⟨i,b⟩ else 0)) =
      if i = one then ∑ b : Sym (Fin n) 1, phiM x ⟨one,b⟩ * phiM y ⟨one,b⟩ else 0 := by
    by_cases h : i = one
    · subst i; simp [one]
    · have hi : (i : ℕ) ≠ 1 := by intro hi; apply h; exact Fin.ext hi
      simp [h, hi]
  simp_rw [hm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← (Sym.oneEquiv : Fin n ≃ Sym (Fin n) 1).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  simp [phiM, BstLean.Part36.monoVal]

lemma tauR_lower56 (d : ℕ) (hd : 1 ≤ d) (v x : Fin n → ℝ)
    (hv : UnitV v) (hx : UnitV x) :
    1 - (∑ a, x a * v a) ^ 2 ≤ tauR d v x := by
  classical
  have hmem : 1 ∈ Finset.Icc 1 d := by simp [hd]
  have hle := Finset.single_le_sum (s := Finset.Icc 1 d)
    (f := fun j => kJ d j x x - kJ d j x v * kJ d j x v / kJ d j v v)
    (fun j _ => residual_diag_nonneg56 d j v x) hmem
  have hv' : (∑ a, v a * v a) = 1 := by simpa only [UnitV, pow_two] using hv
  have hx' : (∑ a, x a * x a) = 1 := by simpa only [UnitV, pow_two] using hx
  simpa only [tauR, KR, kJ_one56 d hd, hv', hx', div_one, pow_two] using hle

lemma residual_power_lower56 (d k c : ℕ) (hd : 1 ≤ d) (hc : c ≤ k)
    (v x : Fin n → ℝ) (hv : UnitV v) (hx : UnitV x) :
    (1 - (∑ a, x a * v a) ^ 2) ^ k ≤ tauR d v x ^ c := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x v
  have hx' : (∑ a, x a ^ 2) = 1 := hx
  have hv' : (∑ a, v a ^ 2) = 1 := hv
  have hcs' : (∑ a, x a * v a) ^ 2 ≤ 1 := by
    simpa only [hx', hv', mul_one] using hcs
  have hzero : 0 ≤ 1 - (∑ a, x a * v a) ^ 2 := by linarith
  have hone : 1 - (∑ a, x a * v a) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (∑ a, x a * v a)]
  exact (pow_le_pow_of_le_one hzero hone hc).trans
    (pow_le_pow_left₀ hzero (tauR_lower56 d hd v x hv hx) c)

end BstLean.Part56
