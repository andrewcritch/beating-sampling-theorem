import BstLean.Part90Defs
import BstLean.Part82Sphere
import BstLean.Part89QInst
import BstLean.Part61LemmaW_Kernel

/-!
# Part 90: closed forms of the block kernels at `d = 3` and bounds of the residual kernel

`closedForms : ClosedForms n`, `kernelUp3 : KernelUp3 n` (and the sharper `kernelUp3'`),
`kernelLow3 : KernelLow3 n`.
-/

namespace BstLean.Part90

open BstLean.Part41 (Mono)
open BstLean.Part56 (UnitV kJ tauR KR)

namespace KerAux

variable {n : ℕ}

/-- The block kernel is the complete homogeneous sum of `x_i y_i`. -/
lemma kJ3_hh (j : ℕ) (hj : j ≤ 3) (x y : Fin n → ℝ) :
    kJ 3 j x y = BstLean.Part82.SphAux.hh (Fin n) j (fun i => x i * y i) := by
  rw [BstLean.Part61.W.kJ_hval (d := 3) j hj x y, BstLean.Part58.Kappa.hval_eq]
  unfold BstLean.Part82.SphAux.hh
  exact BstLean.Part82.SphAux.sum_univ_inst _ _ _

lemma k0 (x y : Fin n → ℝ) : kJ 3 0 x y = 1 := by
  rw [kJ3_hh 0 (by norm_num), BstLean.Part82.SphAux.hh_zero]

lemma k1 (x y : Fin n → ℝ) : kJ 3 1 x y = ∑ i, x i * y i := by
  rw [kJ3_hh 1 (by norm_num)]
  exact (BstLean.Part82.SphAux.hForm (Fin n) inferInstance (fun i => x i * y i)).1

lemma k2 (x y : Fin n → ℝ) :
    kJ 3 2 x y = ((∑ i, x i * y i) ^ 2 + ∑ i, (x i * y i) ^ 2) / 2 := by
  rw [kJ3_hh 2 (by norm_num)]
  exact (BstLean.Part82.SphAux.hForm (Fin n) inferInstance (fun i => x i * y i)).2.1

lemma k3 (x y : Fin n → ℝ) :
    kJ 3 3 x y = ((∑ i, x i * y i) ^ 3 + 3 * (∑ i, x i * y i) * (∑ i, (x i * y i) ^ 2) +
      2 * ∑ i, (x i * y i) ^ 3) / 6 := by
  rw [kJ3_hh 3 (by norm_num)]
  exact (BstLean.Part82.SphAux.hForm (Fin n) inferInstance (fun i => x i * y i)).2.2

lemma tau_expand (v x : Fin n → ℝ) :
    tauR 3 v x = (kJ 3 1 x x - kJ 3 1 x v * kJ 3 1 x v / kJ 3 1 v v) +
      ((kJ 3 2 x x - kJ 3 2 x v * kJ 3 2 x v / kJ 3 2 v v) +
       (kJ 3 3 x x - kJ 3 3 x v * kJ 3 3 x v / kJ 3 3 v v)) := by
  unfold tauR KR
  have hI : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  rw [hI, Finset.sum_insert (by decide), Finset.sum_pair (by decide)]

lemma lin3 {ι : Type} (S : Finset ι) (f a b c : ι → ℝ) (α β γ : ℝ)
    (h : ∀ i, f i = α * a i - β * b i + γ * c i) :
    ∑ i ∈ S, f i = α * ∑ i ∈ S, a i - β * ∑ i ∈ S, b i + γ * ∑ i ∈ S, c i := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => h i

section sphere
variable (v x : Fin n → ℝ) (s : ℝ) (hv : ∑ i, v i ^ 2 = 1) (hx : ∑ i, x i ^ 2 = 1)
  (hs : ∑ i, v i * x i = s)
include hv hx hs

lemma step (P Q c : ℝ) :
    ∑ k, (P * x k - c * (Q * v k)) ^ 2 = P ^ 2 - 2 * c * P * Q * s + c ^ 2 * Q ^ 2 := by
  rw [lin3 Finset.univ _ (fun k => x k ^ 2) (fun k => v k * x k) (fun k => v k ^ 2)
    (P ^ 2) (2 * c * P * Q) (c ^ 2 * Q ^ 2) (fun k => by ring), hx, hv, hs]
  ring

lemma full2 : ∑ i, ∑ l, (x i * x l - s ^ 2 * (v i * v l)) ^ 2 = 1 - s ^ 4 := by
  simp only [step v x s hv hx hs]
  rw [lin3 Finset.univ _ (fun k => x k ^ 2) (fun k => v k * x k) (fun k => v k ^ 2)
    1 (2 * s ^ 3) (s ^ 4) (fun k => by ring), hx, hv, hs]
  ring

lemma full3 :
    ∑ i, ∑ l, ∑ k, (x i * x l * x k - s ^ 3 * (v i * v l * v k)) ^ 2 = 1 - s ^ 6 := by
  simp only [step v x s hv hx hs]
  have h1 : ∀ i, ∑ l, ((x i * x l) ^ 2 - 2 * s ^ 3 * (x i * x l) * (v i * v l) * s +
      (s ^ 3) ^ 2 * (v i * v l) ^ 2) = x i ^ 2 - 2 * s ^ 5 * (x i * v i) + s ^ 6 * v i ^ 2 := by
    intro i
    rw [lin3 Finset.univ _ (fun k => x k ^ 2) (fun k => v k * x k) (fun k => v k ^ 2)
      (x i ^ 2) (2 * s ^ 4 * (x i * v i)) (s ^ 6 * v i ^ 2) (fun k => by ring), hx, hv, hs]
    ring
  simp only [h1]
  rw [lin3 Finset.univ _ (fun k => x k ^ 2) (fun k => v k * x k) (fun k => v k ^ 2)
    1 (2 * s ^ 5) (s ^ 6) (fun k => by ring), hx, hv, hs]
  ring

/-- Diagonal of the pair sum. -/
lemma D2 : ∑ i, (x i * x i) ^ 2 - 2 * s ^ 2 * ∑ i, (x i * v i) ^ 2 +
    s ^ 4 * ∑ i, (v i * v i) ^ 2 ≤ 1 - s ^ 4 := by
  have e : ∑ i, (x i * x i - s ^ 2 * (v i * v i)) ^ 2 =
      1 * ∑ i, (x i * x i) ^ 2 - 2 * s ^ 2 * ∑ i, (x i * v i) ^ 2 +
        s ^ 4 * ∑ i, (v i * v i) ^ 2 :=
    lin3 Finset.univ _ _ _ _ _ _ _ (fun i => by ring)
  have le : ∑ i, (x i * x i - s ^ 2 * (v i * v i)) ^ 2 ≤
      ∑ i, ∑ l, (x i * x l - s ^ 2 * (v i * v l)) ^ 2 :=
    Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun l => (x i * x l - s ^ 2 * (v i * v l)) ^ 2)
        (fun l _ => sq_nonneg _) (Finset.mem_univ i)
  rw [full2 v x s hv hx hs] at le
  linarith

/-- The triples `(i, i, i)`. -/
lemma D3a : ∑ i, (x i * x i) ^ 3 - 2 * s ^ 3 * ∑ i, (x i * v i) ^ 3 +
    s ^ 6 * ∑ i, (v i * v i) ^ 3 ≤ 1 - s ^ 6 := by
  have e : ∑ i, (x i * x i * x i - s ^ 3 * (v i * v i * v i)) ^ 2 =
      1 * ∑ i, (x i * x i) ^ 3 - 2 * s ^ 3 * ∑ i, (x i * v i) ^ 3 +
        s ^ 6 * ∑ i, (v i * v i) ^ 3 :=
    lin3 Finset.univ _ _ _ _ _ _ _ (fun i => by ring)
  have le : ∑ i, (x i * x i * x i - s ^ 3 * (v i * v i * v i)) ^ 2 ≤
      ∑ i, ∑ l, ∑ k, (x i * x l * x k - s ^ 3 * (v i * v l * v k)) ^ 2 :=
    Finset.sum_le_sum fun i _ =>
      (Finset.single_le_sum (f := fun k => (x i * x i * x k - s ^ 3 * (v i * v i * v k)) ^ 2)
        (fun l _ => sq_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum
        (f := fun l => ∑ k, (x i * x l * x k - s ^ 3 * (v i * v l * v k)) ^ 2)
        (fun l _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ i))
  rw [full3 v x s hv hx hs] at le
  linarith

/-- The triples `(i, i, k)`. -/
lemma D3b : ∑ i, (x i * x i) ^ 2 - 2 * s ^ 4 * ∑ i, (x i * v i) ^ 2 +
    s ^ 6 * ∑ i, (v i * v i) ^ 2 ≤ 1 - s ^ 6 := by
  have e : ∑ i, ∑ k, (x i * x i * x k - s ^ 3 * (v i * v i * v k)) ^ 2 =
      1 * ∑ i, (x i * x i) ^ 2 - 2 * s ^ 4 * ∑ i, (x i * v i) ^ 2 +
        s ^ 6 * ∑ i, (v i * v i) ^ 2 := by
    simp only [step v x s hv hx hs]
    exact lin3 Finset.univ _ _ _ _ _ _ _ (fun i => by ring)
  have le : ∑ i, ∑ k, (x i * x i * x k - s ^ 3 * (v i * v i * v k)) ^ 2 ≤
      ∑ i, ∑ l, ∑ k, (x i * x l * x k - s ^ 3 * (v i * v l * v k)) ^ 2 :=
    Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum
        (f := fun l => ∑ k, (x i * x l * x k - s ^ 3 * (v i * v l * v k)) ^ 2)
        (fun l _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ i)
  rw [full3 v x s hv hx hs] at le
  linarith

lemma s_sq_le : s ^ 2 ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v x
  rw [hx, hv, hs] at h
  linarith

end sphere

lemma blockUp (A B C lam : ℝ) (hC : 0 < C) :
    A - B * B / C ≤ A - 2 * lam * B + lam ^ 2 * C := by
  have : 2 * lam * B - lam ^ 2 * C ≤ B * B / C := by
    rw [le_div_iff₀ hC]
    nlinarith [sq_nonneg (B - lam * C)]
  linarith

/-- The three blocks of the residual kernel are at most `1 − s²`, `1 − s⁴`, `1 − s⁶`. -/
lemma blocks_up (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    kJ 3 1 x x - kJ 3 1 x v * kJ 3 1 x v / kJ 3 1 v v ≤ 1 - (∑ i, v i * x i) ^ 2 ∧
    kJ 3 2 x x - kJ 3 2 x v * kJ 3 2 x v / kJ 3 2 v v ≤ 1 - (∑ i, v i * x i) ^ 4 ∧
    kJ 3 3 x x - kJ 3 3 x v * kJ 3 3 x v / kJ 3 3 v v ≤ 1 - (∑ i, v i * x i) ^ 6 := by
  have hv1 : ∑ i, v i ^ 2 = 1 := hv
  have hv' : ∑ i, v i * v i = 1 := by simpa [sq] using hv1
  have hx' : ∑ i, x i * x i = 1 := by simpa [sq] using hx
  have hsw : ∑ i, x i * v i = ∑ i, v i * x i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  set s : ℝ := ∑ i, v i * x i with hs
  have d2 := D2 v x s hv1 hx hs.symm
  have d3a := D3a v x s hv1 hx hs.symm
  have d3b := D3b v x s hv1 hx hs.symm
  have p1 := BstLean.Part56.Orth.block_norm_pos (d := 3) v hv 1 (by norm_num)
  have p2 := BstLean.Part56.Orth.block_norm_pos (d := 3) v hv 2 (by norm_num)
  have p3 := BstLean.Part56.Orth.block_norm_pos (d := 3) v hv 3 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · refine (blockUp _ _ _ (s ^ 1) p1).trans ?_
    rw [k1, k1, k1, hx', hv', hsw]
    apply le_of_eq; ring
  · refine (blockUp _ _ _ (s ^ 2) p2).trans ?_
    rw [k2, k2, k2, hx', hv', hsw]
    linarith
  · refine (blockUp _ _ _ (s ^ 3) p3).trans ?_
    rw [k3, k3, k3, hx', hv', hsw]
    linarith

end KerAux

open KerAux

/-- **Closed forms of the block kernels** at `d = 3`. -/
theorem closedForms (n : ℕ) : ClosedForms n := by
  refine ⟨fun x y => ⟨k0 x y, k1 x y, k2 x y, k3 x y⟩, ?_⟩
  intro v hv x hx
  have hx' : ∑ i, x i * x i = 1 := by simpa [sq] using hx
  have hb : ∀ j, bF v j x ^ 2 = kJ 3 j x v * kJ 3 j x v / kJ 3 j v v := by
    intro j
    unfold bF
    rw [div_pow, Real.sq_sqrt (BstLean.Part89.kJ_self_nonneg 3 j v), sq]
  have a2 : ∑ i, (x i * x i) ^ 2 = ∑ i, x i ^ 4 := Finset.sum_congr rfl fun i _ => by ring
  have a3 : ∑ i, (x i * x i) ^ 3 = ∑ i, x i ^ 6 := Finset.sum_congr rfl fun i _ => by ring
  rw [tau_expand, hb 1, hb 2, hb 3, k1 x x, k2 x x, k3 x x, hx', a2, a3]
  ring

/-- Sharper upper bound: `τ(x) ≤ (1 − s²)(3 + 2s² + s⁴)`. -/
theorem kernelUp3' (n : ℕ) :
    ∀ v : Fin n → ℝ, UnitV v → ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 →
      tauR 3 v x ≤ (1 - (∑ i, v i * x i) ^ 2) *
        (3 + 2 * (∑ i, v i * x i) ^ 2 + (∑ i, v i * x i) ^ 4) := by
  intro v hv x hx
  obtain ⟨h1, h2, h3⟩ := blocks_up v hv x hx
  rw [tau_expand]
  have e : (1 - (∑ i, v i * x i) ^ 2) *
      (3 + 2 * (∑ i, v i * x i) ^ 2 + (∑ i, v i * x i) ^ 4) =
      (1 - (∑ i, v i * x i) ^ 2) + ((1 - (∑ i, v i * x i) ^ 4) +
        (1 - (∑ i, v i * x i) ^ 6)) := by ring
  rw [e]
  linarith

/-- **Upper bound of the residual kernel** on the sphere. -/
theorem kernelUp3 (n : ℕ) : KernelUp3 n := by
  intro v hv x hx
  refine (kernelUp3' n v hv x hx).trans ?_
  have hs1 := s_sq_le v x _ hv hx rfl
  nlinarith [sq_nonneg ((∑ i, v i * x i) ^ 2), sq_nonneg (∑ i, v i * x i),
    mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg (∑ i, v i * x i)),
    mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg ((∑ i, v i * x i) ^ 2))]

/-- **Lower bound of the residual kernel** on the sphere. -/
theorem kernelLow3 (n : ℕ) : KernelLow3 n := by
  intro v hv x hx
  have hv1 : ∑ i, v i ^ 2 = 1 := hv
  have hv' : ∑ i, v i * v i = 1 := by simpa [sq] using hv1
  have hx' : ∑ i, x i * x i = 1 := by simpa [sq] using hx
  have hsw : ∑ i, x i * v i = ∑ i, v i * x i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  set s : ℝ := ∑ i, v i * x i with hs
  set qx : ℝ := ∑ i, (x i * x i) ^ 2 with hqx
  set qv : ℝ := ∑ i, (v i * v i) ^ 2 with hqv
  set w : ℝ := ∑ i, (x i * v i) ^ 2 with hw
  have p2 := BstLean.Part56.Orth.block_norm_pos (d := 3) v hv 2 (by norm_num)
  have p3 := BstLean.Part56.Orth.block_norm_pos (d := 3) v hv 3 (by norm_num)
  have hA : kJ 3 2 x x = (1 + qx) / 2 := by rw [k2, hx']; ring
  have hB : kJ 3 2 x v = (s ^ 2 + w) / 2 := by rw [k2, hsw]
  have hCv : kJ 3 2 v v = (1 + qv) / 2 := by rw [k2, hv']; ring
  have hqv0 : 0 < 1 + qv := by rw [hCv] at p2; linarith
  have hcs : (s ^ 2 + w) ^ 2 ≤ (s ^ 4 + qx) * (1 + qv) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Option (Fin n)))
      (fun o => Option.elim o (s ^ 2) (fun i => x i * x i))
      (fun o => Option.elim o 1 (fun i => v i * v i))
    simp only [Fintype.sum_option, Option.elim_none, Option.elim_some] at h
    have e1 : ∑ i, x i * x i * (v i * v i) = w := Finset.sum_congr rfl fun i _ => by ring
    rw [e1] at h
    nlinarith [h]
  have hq : (s ^ 2 + w) / 2 * ((s ^ 2 + w) / 2) / ((1 + qv) / 2) ≤ (s ^ 4 + qx) / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : 0 ≤ kJ 3 3 x x - kJ 3 3 x v * kJ 3 3 x v / kJ 3 3 v v := by
    rw [sub_nonneg, div_le_iff₀ p3]
    have := BstLean.Part89.kJ_cs 3 3 x v
    nlinarith
  rw [tau_expand, k1, k1, k1, hx', hv', hsw, hA, hB, hCv]
  nlinarith

end BstLean.Part90

#print axioms BstLean.Part90.closedForms
#print axioms BstLean.Part90.kernelUp3
#print axioms BstLean.Part90.kernelUp3'
#print axioms BstLean.Part90.kernelLow3
