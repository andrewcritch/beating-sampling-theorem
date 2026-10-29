import BstLean.Part56MomProg_Scalar

/-! Polynomial form and degree bounds for every weight, including unused keys. -/

namespace BstLean.Part56.MomProg

open BstLean.Part56
open BstLean.Part41 (Mono phiM)
open MvPolynomial
open MeasureTheory

variable {n d : ℕ}

noncomputable def monoPoly (p : Mono n d) : MvPolynomial (Fin n) ℝ :=
  (p.2.val.map fun a => (X a : MvPolynomial (Fin n) ℝ)).prod

theorem monoPoly_eval (p : Mono n d) (x : Fin n → ℝ) :
    eval x (monoPoly p) = phiM x p := by
  simp [monoPoly, phiM, BstLean.Part36.monoVal, map_multiset_prod, Multiset.map_map]

theorem monoPoly_degree (p : Mono n d) : (monoPoly p).totalDegree ≤ (p.1 : ℕ) := by
  have h := totalDegree_multiset_prod (p.2.val.map fun a => (X a : MvPolynomial (Fin n) ℝ))
  simpa [monoPoly, Multiset.map_map, p.2.property] using h

noncomputable def kernelPoly (d j : ℕ) (v : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ p : Mono n d, if (p.1 : ℕ) = j then C (phiM v p) * monoPoly p else 0

noncomputable def diagPoly (n d j : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ p : Mono n d, if (p.1 : ℕ) = j then monoPoly p ^ 2 else 0

noncomputable def betaPoly (d j : ℕ) (v : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  C (1 / kJ d j v v) * kernelPoly d j v

noncomputable def tauPoly (d : ℕ) (v : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ Finset.Icc 1 d, (diagPoly n d j - C (1 / kJ d j v v) * kernelPoly d j v ^ 2)

noncomputable def weightPoly {k : ℕ} (v : Fin n → ℝ) (κ : KeyRK k d) : MvPolynomial (Fin n) ℝ :=
  tauPoly d v ^ (κ.1.2 : ℕ) * ∏ r, betaPoly d (κ.2 r) v

theorem kernelPoly_eval (d j : ℕ) (v x : Fin n → ℝ) :
    eval x (kernelPoly d j v) = kJ d j x v := by
  classical
  simp only [kernelPoly, map_sum]
  unfold kJ
  apply Finset.sum_congr rfl
  intro p _
  split_ifs with hp <;> simp [phiB, hp, monoPoly_eval, mul_comm]

theorem diagPoly_eval (d j : ℕ) (x : Fin n → ℝ) :
    eval x (diagPoly n d j) = kJ d j x x := by
  classical
  simp only [diagPoly, map_sum]
  unfold kJ
  apply Finset.sum_congr rfl
  intro p _
  split_ifs with hp <;> simp [phiB, hp, monoPoly_eval, pow_two]

theorem betaPoly_eval (d j : ℕ) (v x : Fin n → ℝ) :
    eval x (betaPoly d j v) = betaJ d j v x := by
  simp [betaPoly, betaJ, kernelPoly_eval, div_eq_mul_inv, mul_comm]

theorem tauPoly_eval (d : ℕ) (v x : Fin n → ℝ) :
    eval x (tauPoly d v) = tauR d v x := by
  simp [tauPoly, tauR, KR, kernelPoly_eval, diagPoly_eval, pow_two, div_eq_mul_inv, mul_comm]

theorem weightPoly_eval {k : ℕ} (v x : Fin n → ℝ) (κ : KeyRK k d) :
    eval x (weightPoly v κ) = tauR d v x ^ (κ.1.2 : ℕ) * ∏ r, betaJ d (κ.2 r) v x := by
  simp [weightPoly, tauPoly_eval, betaPoly_eval]

theorem kernelPoly_degree (d j : ℕ) (v : Fin n → ℝ) :
    (kernelPoly d j v).totalDegree ≤ j := by
  classical
  apply totalDegree_finsetSum_le
  intro p _
  split_ifs with hp
  · exact (totalDegree_mul _ _).trans (by simpa [hp] using monoPoly_degree p)
  · simp

theorem diagPoly_degree (d j : ℕ) : (diagPoly n d j).totalDegree ≤ 2 * j := by
  classical
  apply totalDegree_finsetSum_le
  intro p _
  split_ifs with hp
  · exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (hp ▸ monoPoly_degree p))
  · simp

theorem betaPoly_degree (d j : ℕ) (v : Fin n → ℝ) :
    (betaPoly d j v).totalDegree ≤ j :=
  (totalDegree_mul _ _).trans (by simpa using kernelPoly_degree d j v)

theorem tauPoly_degree (d : ℕ) (v : Fin n → ℝ) : (tauPoly d v).totalDegree ≤ 2 * d := by
  unfold tauPoly
  apply totalDegree_finsetSum_le
  intro j hj
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (diagPoly_degree d j).trans (Nat.mul_le_mul_left 2 (Finset.mem_Icc.mp hj).2)
  · apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2
      ((kernelPoly_degree d j v).trans (Finset.mem_Icc.mp hj).2))

theorem weightPoly_degree {k : ℕ} (v : Fin n → ℝ) (κ : KeyRK k d) :
    (weightPoly v κ).totalDegree ≤ d * (2 * (κ.1.2 : ℕ) + ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ))) := by
  apply (totalDegree_mul _ _).trans
  have hτ := (totalDegree_pow (tauPoly d v) (κ.1.2 : ℕ)).trans
    (Nat.mul_le_mul_left _ (tauPoly_degree d v))
  have hβ := totalDegree_finsetProd Finset.univ (fun r => betaPoly d (κ.2 r) v)
  have hs : (∑ r, (betaPoly d (κ.2 r) v).totalDegree) ≤
      ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ)) * d := by
    calc
      _ ≤ ∑ r : Fin ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ)), d := by
        apply Finset.sum_le_sum
        intro r _
        exact (betaPoly_degree d (κ.2 r) v).trans (Nat.le_of_lt_succ (κ.2 r).isLt)
      _ = _ := by simp
  nlinarith [hβ.trans hs]

theorem weightPoly_degree_all {k : ℕ} (v : Fin n → ℝ) (κ : KeyRK k d) :
    (weightPoly v κ).totalDegree ≤ 2 * d * k := by
  apply (weightPoly_degree v κ).trans
  have hi : (κ.1.1 : ℕ) ≤ k := Nat.le_of_lt_succ κ.1.1.isLt
  have hl : (κ.1.2 : ℕ) ≤ k := Nat.le_of_lt_succ κ.1.2.isLt
  have hb : 2 * (κ.1.2 : ℕ) + ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ)) ≤ 2 * k := by omega
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul_left d hb

theorem weightPoly_degree_used {k : ℕ} (v : Fin n → ℝ) (κ : KeyRK k d)
    (hκ : 2 * (κ.1.2 : ℕ) ≤ (κ.1.1 : ℕ)) : (weightPoly v κ).totalDegree ≤ d * k := by
  apply (weightPoly_degree v κ).trans
  rw [Nat.add_sub_of_le hκ]
  exact Nat.mul_le_mul_left d (Nat.le_of_lt_succ κ.1.1.isLt)

theorem surrogate_weight_ratio {k : ℕ} (hn : 1 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (v : Fin n → ℝ) (hv : UnitV v) (κ : KeyRK k d) :
    wRK (surrRK n K t v) d v κ =
      wickC κ.1.1 κ.1.2 * (1 / BstLean.Part36.DD n d) ^ (κ.1.2 : ℕ) *
        ((∫ x, eval x (weightPoly v κ) *
          BstLean.Part37.taylorExp K (t * (∑ i, v i * x i) ^ 2)
          ∂BstLean.Part29.uniformSphere n) / scalarTilt n K 0 t) := by
  unfold wRK
  rw [sg_sq hn]
  simp_rw [← weightPoly_eval]
  rw [integral_surrogate hn K t ht v, scalarTilt_normalizer hn K t v hv]

end BstLean.Part56.MomProg
