import BstLean.Part56Defs
import BstLean.Part50Laws
import BstLean.Part36Index

/-! Algebra and denominator facts for the Part 56 moment program. -/

namespace BstLean.Part56.MomProg

open MeasureTheory BstLean.Cost
open BstLean.Part56
open BstLean.Part41 (Mono phiM heavyCount)
open BstLean.Part29 (uniformSphere)

variable {n d : ℕ}

theorem qA_rk1 (t : ℝ) (v x : Fin n → ℝ) :
    BstLean.Part50.qA (rk1 t v) x = t * (∑ i, v i * x i) ^ 2 := by
  classical
  unfold BstLean.Part50.qA rk1
  simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rk1_psd (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) :
    BstLean.Part50.PSDq (rk1 t v) := by
  intro x
  rw [qA_rk1]
  exact mul_nonneg ht (sq_nonneg _)

theorem surrRK_sphLaw (hn : 1 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (v : Fin n → ℝ) : BstLean.Part40.SphLaw n (surrRK n K t v) :=
  (BstLean.Part50.binghamKA_antipodal hn K (rk1 t v) (rk1_psd t ht v)).1

theorem kJ_pos (v : Fin n → ℝ) (hv : UnitV v) (j : ℕ) (hj : j ≤ d) :
    0 < kJ d j v v := by
  classical
  have hex : ∃ a, v a ≠ 0 := by
    by_contra h
    push Not at h
    have : (∑ a, v a ^ 2) = 0 := by simp [h]
    rw [hv] at this
    norm_num at this
  obtain ⟨a, ha⟩ := hex
  let p : Mono n d := ⟨⟨j, by omega⟩, Sym.replicate j a⟩
  have hp : phiB d j v p = v a ^ j := by
    simp [p, phiB, phiM, BstLean.Part36.monoVal, Sym.replicate]
  have hterm : 0 < phiB d j v p * phiB d j v p := by
    rw [hp]
    exact mul_self_pos.mpr (pow_ne_zero _ ha)
  exact lt_of_lt_of_le hterm (Finset.single_le_sum
    (fun q _ => mul_self_nonneg (phiB d j v q)) (Finset.mem_univ p))

theorem sg_sq (hn : 1 ≤ n) : BstLean.Part53.sg n d ^ 2 = 1 / BstLean.Part36.DD n d := by
  have hD := BstLean.Part36.DD_pos (d := d) hn
  rw [BstLean.Part53.sg, div_pow, one_pow, Real.sq_sqrt hD.le]

theorem onceCost_nonneg (n d k K : ℕ) : 0 ≤ onceCost56 n d k K := by
  unfold onceCost56
  positivity

theorem phiB_zero_indep (x y : Fin n → ℝ) (p : Mono n d) :
    phiB d 0 x p = phiB d 0 y p := by
  classical
  unfold phiB
  split_ifs with hp
  · have hm : p.2.val = 0 := Multiset.card_eq_zero.mp (p.2.property.trans hp)
    change (Multiset.map x p.2.val).prod = (Multiset.map y p.2.val).prod
    rw [hm]
    simp
  · rfl

theorem betaJ_zero (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    betaJ d 0 v x = 1 := by
  have h : kJ d 0 x v = kJ d 0 v v := by
    unfold kJ
    apply Finset.sum_congr rfl
    intro p _
    rw [phiB_zero_indep x v p]
  unfold betaJ
  rw [h, div_self (kJ_pos v hv 0 (Nat.zero_le d)).ne']

theorem wRK_d_zero (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    {k : ℕ} (v : Fin n → ℝ) (hv : UnitV v) (κ : KeyRK k 0) :
    wRK μ 0 v κ = if (κ.1.2 : ℕ) = 0 then 1 else 0 := by
  classical
  have hτ (x : Fin n → ℝ) : tauR 0 v x = 0 := by simp [tauR, KR]
  have hβ (r : Fin ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ))) (x : Fin n → ℝ) :
      betaJ 0 (κ.2 r) v x = 1 := by
    have hj : (κ.2 r : ℕ) = 0 := by have := (κ.2 r).isLt; omega
    rw [hj]
    exact betaJ_zero v hv x
  by_cases hl : (κ.1.2 : ℕ) = 0
  · have hf : ((κ.1.1 : ℕ).factorial : ℝ) ≠ 0 := by positivity
    simp [wRK, wickC, hl, hτ, betaJ_zero v hv, hf]
  · simp [wRK, hl, hτ, zero_pow hl]

theorem exists_d_zero (n k K : ℕ) (hn : 2 ≤ n) :
    ∃ pm : Prog (InM56 n) (KeyRK k 0), heavyCount pm = 0 ∧ MomSpec56 pm K ∧
      (pm.cost : ℝ) ≤ onceCost56 n 0 k K := by
  classical
  let pm : Prog (InM56 n) (KeyRK k 0) :=
    Prog.ofArgs fun κ => if (κ.1.2 : ℕ) = 0 then .cst 1 else .cst 0
  refine ⟨pm, ?_, ?_, ?_⟩
  · unfold heavyCount
    simp only [pm, Prog.ofArgs, List.map_nil, List.sum_nil, zero_add]
    apply Finset.sum_eq_zero
    intro κ _
    split_ifs <;> simp [BstLean.Part41.argHeavy]
  · intro t v ht hv κ
    have hμ := surrRK_sphLaw (by omega : 1 ≤ n) K t ht v
    have := hμ.1
    rw [wRK_d_zero _ v hv κ]
    simp only [pm, Prog.eval, Prog.ofArgs, run]
    split_ifs <;> simp [Arg.eval]
  · simpa [pm] using onceCost_nonneg n 0 k K

theorem wRK_k_zero (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (v : Fin n → ℝ) (κ : KeyRK 0 d) : wRK μ d v κ = 1 := by
  simp [wRK, wickC]

theorem exists_k_zero (n d K : ℕ) (hn : 2 ≤ n) :
    ∃ pm : Prog (InM56 n) (KeyRK 0 d), heavyCount pm = 0 ∧ MomSpec56 pm K ∧
      (pm.cost : ℝ) ≤ onceCost56 n d 0 K := by
  let pm : Prog (InM56 n) (KeyRK 0 d) := Prog.ofArgs fun _ => .cst 1
  refine ⟨pm, ?_, ?_, ?_⟩
  · simp [pm, heavyCount, Prog.ofArgs, BstLean.Part41.argHeavy]
  · intro t v ht hv κ
    have hμ := surrRK_sphLaw (by omega : 1 ≤ n) K t ht v
    have := hμ.1
    simpa [pm, Prog.eval, Prog.ofArgs, Arg.eval, run] using
      (wRK_k_zero (surrRK n K t v) v κ).symm
  · simpa [pm] using onceCost_nonneg n d 0 K

end BstLean.Part56.MomProg
