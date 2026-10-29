import BstLean.Part56Defs

/-! Algebra of the residual Gram kernel for Part 56, Prop D. -/
namespace BstLean.Part56

open MeasureTheory
open BstLean.Part41 (Mono)

variable {n d : ℕ}

/-- The residual vector in one homogeneous block. -/
noncomputable def residualB (d j : ℕ) (v x : Fin n → ℝ) : Mono n d → ℝ :=
  fun p => phiB d j x p - betaJ d j v x * phiB d j v p

private lemma dot_self_zero {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (h : ∑ p, a p * a p = 0) : ∀ p, a p = 0 := by
  classical
  have hs : ∑ p, a p ^ 2 = 0 := by simpa only [pow_two] using h
  exact fun p => ((Finset.sum_sq_eq_zero_iff Finset.univ a).mp hs) p (Finset.mem_univ p)

/-- Each residual block has the regression kernel, including a zero anchor. -/
theorem residualB_gram (d j : ℕ) (v x y : Fin n → ℝ) :
    (∑ p : Mono n d, residualB d j v x p * residualB d j v y p) =
      kJ d j x y - kJ d j x v * kJ d j y v / kJ d j v v := by
  classical
  have hsym : kJ d j v y = kJ d j y v := by
    unfold kJ
    apply Finset.sum_congr rfl
    intro p _
    ring
  by_cases hz : kJ d j v v = 0
  · have hv : ∀ p, phiB d j v p = 0 := dot_self_zero _ hz
    simp [residualB, betaJ, hv, kJ]
  · have he : (∑ p : Mono n d, residualB d j v x p * residualB d j v y p) =
        kJ d j x y - betaJ d j v y * kJ d j x v -
          betaJ d j v x * kJ d j v y +
          betaJ d j v x * betaJ d j v y * kJ d j v v := by
      have hexp : ∀ p : Mono n d,
          residualB d j v x p * residualB d j v y p =
            phiB d j x p * phiB d j y p -
              betaJ d j v y * (phiB d j x p * phiB d j v p) -
              betaJ d j v x * (phiB d j v p * phiB d j y p) +
              (betaJ d j v x * betaJ d j v y) * (phiB d j v p * phiB d j v p) := by
        intro p
        unfold residualB
        ring
      simp_rw [hexp]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, kJ]
    rw [he, hsym]
    unfold betaJ
    field_simp
    ring

/-- The full residual kernel is a sum of Gram kernels. -/
theorem KR_gram (d : ℕ) (v x y : Fin n → ℝ) :
    KR d v x y = ∑ j ∈ Finset.Icc 1 d,
      ∑ p : Mono n d, residualB d j v x p * residualB d j v y p := by
  classical
  unfold KR
  apply Finset.sum_congr rfl
  intro j _
  exact (residualB_gram d j v x y).symm

theorem tauR_nonneg (d : ℕ) (v x : Fin n → ℝ) : 0 ≤ tauR d v x := by
  classical
  rw [tauR, KR_gram]
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun p _ => mul_self_nonneg _

/-- Cauchy--Schwarz for the full residual kernel. -/
theorem KR_sq_le (d : ℕ) (v x y : Fin n → ℝ) :
    KR d v x y ^ 2 ≤ tauR d v x * tauR d v y := by
  classical
  let S : Finset (ℕ × Mono n d) := (Finset.Icc 1 d).product Finset.univ
  have h := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun q => residualB d q.1 v x q.2) (fun q => residualB d q.1 v y q.2)
  have he (a b : Fin n → ℝ) :
      (∑ q ∈ S, residualB d q.1 v a q.2 * residualB d q.1 v b q.2) =
        KR d v a b := by
    dsimp only [S]
    exact (Finset.sum_product' (Finset.Icc 1 d) (Finset.univ : Finset (Mono n d))
      (fun j p => residualB d j v a p * residualB d j v b p)).trans
        (KR_gram d v a b).symm
  simpa only [pow_two, he, tauR] using h

/-- The zero-denominator convention gives a correlation in the unit interval. -/
theorem rhoR_sq_le_one (d : ℕ) (v x y : Fin n → ℝ) : rhoR d v x y ^ 2 ≤ 1 := by
  have ht : 0 ≤ tauR d v x * tauR d v y :=
    mul_nonneg (tauR_nonneg d v x) (tauR_nonneg d v y)
  by_cases hz : Real.sqrt (tauR d v x * tauR d v y) = 0
  · simp [rhoR, hz]
  · have hp : 0 < Real.sqrt (tauR d v x * tauR d v y) ^ 2 := sq_pos_of_ne_zero hz
    rw [rhoR, div_pow, div_le_one hp, Real.sq_sqrt ht]
    exact KR_sq_le d v x y

/-- The first homogeneous block is the ordinary Euclidean dot product. -/
theorem kJ_one (d : ℕ) (hd : 1 ≤ d) (x y : Fin n → ℝ) :
    kJ d 1 x y = ∑ a, x a * y a := by
  classical
  let j : Fin (d + 1) := ⟨1, by omega⟩
  have hidx : ∀ i : Fin (d + 1), (i : ℕ) = 1 ↔ i = j := by
    intro i
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  unfold kJ
  rw [Fintype.sum_sigma]
  have hm : ∀ (i : Fin (d + 1)) (b : Sym (Fin n) (i : ℕ)),
      phiB d 1 x ⟨i, b⟩ * phiB d 1 y ⟨i, b⟩ =
        if i = j then BstLean.Part41.phiM x ⟨i, b⟩ *
          BstLean.Part41.phiM y ⟨i, b⟩ else 0 := by
    intro i b
    by_cases h : i = j <;> simp [phiB, hidx, h]
  simp_rw [hm, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  have he := (Sym.oneEquiv : Fin n ≃ Sym (Fin n) 1).sum_comp
    (fun b => BstLean.Part36.monoVal x b.val * BstLean.Part36.monoVal y b.val)
  change (∑ b : Sym (Fin n) 1,
    BstLean.Part36.monoVal x b.val * BstLean.Part36.monoVal y b.val) = _
  rw [← he]
  apply Finset.sum_congr rfl
  intro a _
  change (({a} : Multiset (Fin n)).map x).prod *
    (({a} : Multiset (Fin n)).map y).prod = _
  simp

/-- The first block supplies the squared perpendicular radius. -/
theorem tauR_ge_perp (d : ℕ) (hd : 1 ≤ d) (v x : Fin n → ℝ)
    (hv : UnitV v) (hx : UnitV x) :
    1 - (∑ a, x a * v a) ^ 2 ≤ tauR d v x := by
  classical
  have hmem : 1 ∈ Finset.Icc 1 d := by simp [hd]
  have hle := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.Icc 1 d) =>
      Finset.sum_nonneg fun p (_ : p ∈ Finset.univ) =>
        mul_self_nonneg (residualB d j v x p)) hmem
  rw [← KR_gram, residualB_gram] at hle
  rw [kJ_one d hd, kJ_one d hd, kJ_one d hd] at hle
  change ∑ a, x a ^ 2 = 1 at hx
  change ∑ a, v a ^ 2 = 1 at hv
  simpa only [← pow_two, hx, hv, div_one, tauR] using hle

/-- Removing an anchor does not increase the squared norm of a block. -/
theorem residualB_sq_le (d j : ℕ) (v x : Fin n → ℝ) :
    (∑ p : Mono n d, residualB d j v x p ^ 2) ≤ kJ d j x x := by
  have hv : 0 ≤ kJ d j v v := by
    unfold kJ
    exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
  have hsub : 0 ≤ kJ d j x v ^ 2 / kJ d j v v :=
    div_nonneg (sq_nonneg _) hv
  have he := residualB_gram d j v x x
  simp only [← pow_two] at he
  rw [he]
  linarith

/-- The squared perpendicular radius is nonnegative for two unit vectors. -/
theorem perp_radius_nonneg (v x : Fin n → ℝ) (hv : UnitV v) (hx : UnitV x) :
    0 ≤ 1 - (∑ a, x a * v a) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x v
  change (∑ a, x a * v a) ^ 2 ≤ (∑ a, x a ^ 2) * ∑ a, v a ^ 2 at h
  rw [hx, hv] at h
  linarith

/-- For positive degree, the Key Lemma hypothesis already forces a nonnegative constant. -/
theorem keyConstant_nonneg (d : ℕ) (hd : 1 ≤ d) (CK : ℝ)
    (hK : KeyLemma56 d CK) : 0 ≤ CK := by
  let v : Fin 2 → ℝ := ![1, 0]
  have hv : UnitV v := by norm_num [UnitV, v, Fin.sum_univ_two]
  have h := hK 2 (by omega) v hv 0 0 (by norm_num) (by norm_num)
    1 1 1 hd (by omega) (by omega) (by omega) (by omega)
  have hn : 0 ≤ ∫ g, ∫ g',
      (∑ p : Mono 2 d, PhiJI d 1 1 ((0 : ℝ) • v) (perpDir v g) p *
        PhiJI d 1 1 ((0 : ℝ) • v) (perpDir v g') p) ^ 2
      ∂BstLean.Part29.stdGauss (Fin 2) ∂BstLean.Part29.stdGauss (Fin 2) :=
    integral_nonneg fun g => integral_nonneg fun g' => sq_nonneg _
  norm_num at h
  simp only [zero_smul] at hn
  exact hn.trans h

section Projection

variable {ι : Type*} [Fintype ι]

/-- Orthogonal projection away from one vector; a zero vector gives the identity. -/
noncomputable def projectOff (u a : ι → ℝ) : ι → ℝ := fun p =>
  a p - (∑ q, a q * u q) / (∑ q, u q ^ 2) * u p

/-- The exact squared norm identity for projection away from one vector. -/
theorem projectOff_sq (u a : ι → ℝ) :
    (∑ p, projectOff u a p ^ 2) =
      (∑ p, a p ^ 2) - (∑ p, a p * u p) ^ 2 / (∑ p, u p ^ 2) := by
  classical
  by_cases hz : (∑ p, u p ^ 2) = 0
  · simp [projectOff, hz]
  · let c : ℝ := (∑ p, a p * u p) / (∑ p, u p ^ 2)
    have hexp : ∀ p, projectOff u a p ^ 2 =
        a p ^ 2 - (2 * c) * (a p * u p) + c ^ 2 * u p ^ 2 := by
      intro p
      change (a p - c * u p) ^ 2 = _
      ring
    simp_rw [hexp]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    dsimp only [c]
    field_simp
    ring

/-- Projection away from one vector contracts the squared Euclidean norm. -/
theorem projectOff_sq_le (u a : ι → ℝ) :
    (∑ p, projectOff u a p ^ 2) ≤ ∑ p, a p ^ 2 := by
  rw [projectOff_sq]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- Projection on both sides contracts the squared Frobenius norm. -/
theorem projectOff_frob_le (u : ι → ℝ) (A : ι → ι → ℝ) :
    (∑ i, ∑ j, projectOff u (fun j => projectOff u (fun i => A i j) i) j ^ 2) ≤
      ∑ i, ∑ j, A i j ^ 2 := by
  calc
    _ ≤ ∑ i, ∑ j, projectOff u (fun i => A i j) i ^ 2 :=
      Finset.sum_le_sum fun i _ => projectOff_sq_le u _
    _ = ∑ j, ∑ i, projectOff u (fun i => A i j) i ^ 2 := Finset.sum_comm
    _ ≤ ∑ j, ∑ i, A i j ^ 2 :=
      Finset.sum_le_sum fun j _ => projectOff_sq_le u _
    _ = _ := Finset.sum_comm

end Projection

end BstLean.Part56
