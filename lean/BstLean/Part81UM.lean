import BstLean.Part81UMA
import BstLean.Part81UMC

/-!
# Part 81 (UM): moments of the geometric sums `G_m(q)`, `q = Σ x_i⁴`, uniform in `m`

Part A, B: `BstLean.Part81UMA` (`int_powsum`, `int_sq_powsum`, `q_pow_le`).
Part C: `BstLean.Part81UMC` (`muS_sum1`, `muS_sum2`, `muS_sum3`).
Part D: this file (`int_Gq`, `int_sq_Gq`, `int_qG1`, `int_qG2`, `int_qG3`).
-/

namespace BstLean.Part81.UM

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part81

variable {n : ℕ}

/-- `P_j(x) = Σ_k x_k^{2j}`. -/
def P (j : ℕ) (x : Fin n → ℝ) : ℝ := ∑ k, x k ^ (2 * j)

lemma P_cont (j : ℕ) : Continuous (P (n := n) j) := by unfold P; fun_prop

lemma P_two (x : Fin n → ℝ) : P 2 x = ∑ i, x i ^ 4 := rfl

lemma P_three (x : Fin n → ℝ) : P 3 x = ∑ i, x i ^ 6 := rfl

lemma int_P (hn : 1 ≤ n) (j : ℕ) : ∫ x, P j x ∂uniformSphere n = muS n j := int_powsum n hn j

lemma qpow_le_P (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) (k : ℕ) :
    (∑ i, x i ^ 4) ^ k ≤ P (k + 1) x := q_pow_le n x hx k

lemma int_lin (hn : 1 ≤ n) (c : ℕ → ℝ) (J : ℕ → ℕ) (M : ℕ) :
    ∫ x, ∑ s ∈ Finset.range M, c s * P (J s) x ∂uniformSphere n
      = ∑ s ∈ Finset.range M, c s * muS n (J s) := by
  rw [integral_finsetSum _ (fun s _ => BstLean.Part78.sph_int hn (by
    have := P_cont (n := n) (J s); fun_prop))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_const_mul, int_P hn]

lemma int_lin_sq (hn : 1 ≤ n) (i : Fin n) (c : ℕ → ℝ) (J : ℕ → ℕ) (M : ℕ) :
    ∫ x, ∑ s ∈ Finset.range M, c s * (x i ^ 2 * P (J s) x) ∂uniformSphere n
      = (∑ s ∈ Finset.range M, c s * muS n (J s)) / n := by
  rw [integral_finsetSum _ (fun s _ => BstLean.Part78.sph_int hn (by
    have := P_cont (n := n) (J s); fun_prop))]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_const_mul]
  have := int_sq_powsum n hn i (J s)
  unfold P
  rw [this]; ring

lemma int_le (hn : 1 ≤ n) {f g : (Fin n → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → f x ≤ g x) :
    ∫ x, f x ∂uniformSphere n ≤ ∫ x, g x ∂uniformSphere n := by
  apply integral_mono_ae (BstLean.Part78.sph_int hn hf) (BstLean.Part78.sph_int hn hg)
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  exact h x hx

/-- Product of a finite geometric sum with a polynomial with nonnegative coefficients,
bounded coefficientwise. -/
lemma geom_mul_le (q : ℝ) (hq : 0 ≤ q) (c d : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hd : ∀ k, 0 ≤ d k)
    (h0 : c 0 ≤ d 0) (hs : ∀ s, c (s + 1) + d s ≤ d (s + 1)) (m M : ℕ) :
    (∑ a ∈ Finset.range m, q ^ a) * ∑ k ∈ Finset.range M, c k * q ^ k
      ≤ ∑ s ∈ Finset.range (m + M), d s * q ^ s := by
  induction m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_mul]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hd s) (pow_nonneg hq s)
  | succ m ih =>
    have hB : ∑ k ∈ Finset.range M, c k * q ^ k ≤ ∑ k ∈ Finset.range (m + M + 1), c k * q ^ k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        (fun k _ _ => mul_nonneg (hc k) (pow_nonneg hq k))
    rw [Finset.sum_range_succ'] at hB
    have e1 : ∑ a ∈ Finset.range (m + 1), q ^ a = q * (∑ a ∈ Finset.range m, q ^ a) + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp [pow_succ, mul_comm]
    have e2 : m + 1 + M = m + M + 1 := by omega
    rw [e1, e2, Finset.sum_range_succ']
    have h3 : q * ((∑ a ∈ Finset.range m, q ^ a) * ∑ k ∈ Finset.range M, c k * q ^ k)
        ≤ q * ∑ s ∈ Finset.range (m + M), d s * q ^ s := mul_le_mul_of_nonneg_left ih hq
    have h4 : q * ∑ s ∈ Finset.range (m + M), d s * q ^ s
        + ∑ s ∈ Finset.range (m + M), c (s + 1) * q ^ (s + 1)
        ≤ ∑ s ∈ Finset.range (m + M), d (s + 1) * q ^ (s + 1) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun s _ => ?_
      have hp : 0 ≤ q ^ (s + 1) := pow_nonneg hq _
      have := mul_le_mul_of_nonneg_right (hs s) hp
      have e : q * (d s * q ^ s) = d s * q ^ (s + 1) := by ring
      rw [e]; linarith
    simp only [pow_zero, mul_one] at hB ⊢
    nlinarith [h3, h4, hB, h0]

lemma Gq_nonneg (m : ℕ) (q : ℝ) (hq : 0 ≤ q) : 0 ≤ Gq m q :=
  Finset.sum_nonneg fun k _ => pow_nonneg hq k

lemma Gq_sq_le (m : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    Gq m q ^ 2 ≤ ∑ s ∈ Finset.range (m + 1 + (m + 1)), ((s : ℝ) + 1) * q ^ s := by
  have h := geom_mul_le q hq (fun _ => 1) (fun s => (s : ℝ) + 1) (fun _ => by norm_num)
    (fun s => by positivity) (by norm_num) (fun s => by push_cast; linarith) (m + 1) (m + 1)
  simp only [one_mul] at h
  unfold Gq
  rw [sq]; exact h

lemma Gq_cube_le (m : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    Gq m q ^ 3 ≤ ∑ s ∈ Finset.range (m + 1 + (m + 1 + (m + 1))),
      (((s : ℝ) + 1) * ((s : ℝ) + 2) / 2) * q ^ s := by
  have h := geom_mul_le q hq (fun s => (s : ℝ) + 1) (fun s => ((s : ℝ) + 1) * ((s : ℝ) + 2) / 2)
    (fun s => by positivity) (fun s => by positivity) (by norm_num)
    (fun s => by push_cast; nlinarith) (m + 1) (m + 1 + (m + 1))
  have h2 := Gq_sq_le m q hq
  have h0 := Gq_nonneg m q hq
  calc Gq m q ^ 3 = Gq m q * Gq m q ^ 2 := by ring
    _ ≤ Gq m q * ∑ s ∈ Finset.range (m + 1 + (m + 1)), ((s : ℝ) + 1) * q ^ s := by gcongr
    _ ≤ _ := h

/-- `Σ_{k<M} μ_{k+1} ≤ 1 + 3/n + 16/n²`. -/
lemma sumG (n : ℕ) (hn : 1000 ≤ n) (M : ℕ) :
    ∑ k ∈ Finset.range M, muS n (k + 1) ≤ 1 + 3 / (n : ℝ) + 16 / (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have h1 : ∑ k ∈ Finset.range M, muS n (k + 1) ≤ ∑ k ∈ Finset.range (M + 2), muS n (k + 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun k _ _ => (muS_pos' n hn1 _).le)
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h1
  have h2 := sum1_range n hn M
  have h3 := muS_two_le n hn1
  have h4 := muS_one n hn1
  simp only [zero_add] at h1
  have e : ∑ k ∈ Finset.range M, muS n (k + 1 + 1 + 1) = ∑ k ∈ Finset.range M, muS n (k + 3) := rfl
  rw [e] at h1
  have e2 : muS n (1 + 1) = muS n 2 := rfl
  rw [e2] at h1
  linarith

/-- Pointwise facts on the sphere. -/
lemma sphere_facts (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    0 ≤ ∑ i, x i ^ 4 ∧ 0 ≤ ∑ i, x i ^ 6 ∧ ∑ i, x i ^ 6 ≤ ∑ i, x i ^ 4 := by
  refine ⟨Finset.sum_nonneg fun i _ => by positivity, Finset.sum_nonneg fun i _ => by positivity, ?_⟩
  exact K3.q6_le_q4 x hx

/-- `0 ≤ (q + q6) G ≤ 2 q G`. -/
lemma qG_bounds (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) (m : ℕ) :
    0 ≤ ((∑ i, x i ^ 4) + ∑ i, x i ^ 6) * Gq m (∑ i, x i ^ 4) ∧
    ((∑ i, x i ^ 4) + ∑ i, x i ^ 6) * Gq m (∑ i, x i ^ 4)
      ≤ 2 * (∑ i, x i ^ 4) * Gq m (∑ i, x i ^ 4) := by
  obtain ⟨h1, h2, h3⟩ := sphere_facts x hx
  have hG := Gq_nonneg m _ h1
  constructor
  · positivity
  · apply mul_le_mul_of_nonneg_right _ hG; linarith

end BstLean.Part81.UM

namespace BstLean.Part81

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part81.UM

theorem int_Gq (n : ℕ) (hn : 1000 ≤ n) (m : ℕ) :
    ∫ x, Gq m (∑ i, x i ^ 4) ∂uniformSphere n ≤ 1 + 3 / (n : ℝ) + 16 / (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have h := int_le hn1 (f := fun x : Fin n → ℝ => Gq m (∑ i, x i ^ 4))
    (g := fun x => ∑ s ∈ Finset.range (m + 1), 1 * P (s + 1) x)
    (by unfold Gq; fun_prop)
    (by have := fun j => P_cont (n := n) j; fun_prop)
    (fun x hx => by
      unfold Gq
      refine Finset.sum_le_sum fun k _ => ?_
      rw [one_mul]; exact qpow_le_P x hx k)
  rw [int_lin hn1] at h
  simp only [one_mul] at h
  exact h.trans (sumG n hn _)

theorem int_sq_Gq (n : ℕ) (hn : 1000 ≤ n) (i : Fin n) (m : ℕ) :
    ∫ x, x i ^ 2 * Gq m (∑ k, x k ^ 4) ∂uniformSphere n ≤
      (1 + 3 / (n : ℝ) + 16 / (n : ℝ) ^ 2) / n := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  have h := int_le hn1 (f := fun x : Fin n → ℝ => x i ^ 2 * Gq m (∑ k, x k ^ 4))
    (g := fun x => ∑ s ∈ Finset.range (m + 1), 1 * (x i ^ 2 * P (s + 1) x))
    (by unfold Gq; fun_prop)
    (by have := fun j => P_cont (n := n) j; fun_prop)
    (fun x hx => by
      unfold Gq
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [one_mul]
      exact mul_le_mul_of_nonneg_left (qpow_le_P x hx k) (sq_nonneg _))
  rw [int_lin_sq hn1] at h
  simp only [one_mul] at h
  refine h.trans ?_
  gcongr
  exact sumG n hn _

theorem int_qG1 (n : ℕ) (hn : 1000 ≤ n) (m : ℕ) :
    ∫ x, ((∑ i, x i ^ 4) + ∑ i, x i ^ 6) * Gq m (∑ i, x i ^ 4) ∂uniformSphere n ≤
      3 / (n : ℝ) + 48 / (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hPc := fun j => P_cont (n := n) j
  have h := int_le hn1
    (f := fun x : Fin n → ℝ => ((∑ i, x i ^ 4) + ∑ i, x i ^ 6) * Gq m (∑ i, x i ^ 4))
    (g := fun x => P 2 x + P 3 x + ∑ s ∈ Finset.range m, 2 * P (s + 3) x)
    (by unfold Gq; fun_prop) (by fun_prop)
    (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := sphere_facts x hx
      rw [P_two, P_three]
      set q := ∑ i, x i ^ 4 with hq
      set p := ∑ i, x i ^ 6 with hp
      have eG : Gq m q = ∑ k ∈ Finset.range m, q ^ (k + 1) + 1 := by
        unfold Gq; rw [Finset.sum_range_succ']; simp
      have hS : 0 ≤ ∑ k ∈ Finset.range m, q ^ (k + 1) :=
        Finset.sum_nonneg fun k _ => pow_nonneg h1 _
      have hT : 2 * q * ∑ k ∈ Finset.range m, q ^ (k + 1)
          ≤ ∑ s ∈ Finset.range m, 2 * P (s + 3) x := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        have := qpow_le_P x hx (k + 2)
        rw [← hq] at this
        have e : 2 * q * q ^ (k + 1) = 2 * q ^ (k + 2) := by ring
        rw [e]; linarith
      rw [eG]
      have : (q + p) * (∑ k ∈ Finset.range m, q ^ (k + 1))
          ≤ 2 * q * ∑ k ∈ Finset.range m, q ^ (k + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) hS
      nlinarith)
  have i1 : Integrable (fun x : Fin n → ℝ => P 2 x) (uniformSphere n) :=
    BstLean.Part78.sph_int hn1 (hPc 2)
  have i2 : Integrable (fun x : Fin n → ℝ => P 3 x) (uniformSphere n) :=
    BstLean.Part78.sph_int hn1 (hPc 3)
  have i3 : Integrable (fun x : Fin n → ℝ => ∑ s ∈ Finset.range m, 2 * P (s + 3) x)
      (uniformSphere n) := BstLean.Part78.sph_int hn1 (by fun_prop)
  have i12 : Integrable (fun x : Fin n → ℝ => P 2 x + P 3 x) (uniformSphere n) := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, int_P hn1, int_P hn1, int_lin hn1,
    ← Finset.mul_sum] at h
  have a1 := muS_two_le n hn1
  have a2 := sum1_range n hn 1
  have a3 := sum1_range n hn m
  simp only [Finset.range_one, Finset.sum_singleton, zero_add] at a2
  have e : (48 : ℝ) / (n : ℝ) ^ 2 = 16 / (n : ℝ) ^ 2 + 2 * (16 / (n : ℝ) ^ 2) := by ring
  rw [e]; linarith

theorem int_qG2 (n : ℕ) (hn : 1000 ≤ n) (m : ℕ) :
    ∫ x, (((∑ i, x i ^ 4) + ∑ i, x i ^ 6) * Gq m (∑ i, x i ^ 4)) ^ 2 ∂uniformSphere n ≤
      64 / (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hPc := fun j => P_cont (n := n) j
  have h := int_le hn1
    (f := fun x : Fin n → ℝ => (((∑ i, x i ^ 4) + ∑ i, x i ^ 6) * Gq m (∑ i, x i ^ 4)) ^ 2)
    (g := fun x => ∑ s ∈ Finset.range (m + 1 + (m + 1)), (4 * ((s : ℝ) + 1)) * P (s + 3) x)
    (by unfold Gq; fun_prop) (by fun_prop)
    (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := sphere_facts x hx
      obtain ⟨b1, b2⟩ := qG_bounds x hx m
      set q := ∑ i, x i ^ 4 with hq
      have hsq := Gq_sq_le m q h1
      calc ((q + ∑ i, x i ^ 6) * Gq m q) ^ 2 ≤ (2 * q * Gq m q) ^ 2 := by gcongr
        _ = 4 * q ^ 2 * Gq m q ^ 2 := by ring
        _ ≤ 4 * q ^ 2 * ∑ s ∈ Finset.range (m + 1 + (m + 1)), ((s : ℝ) + 1) * q ^ s := by gcongr
        _ ≤ _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun s _ => ?_
          have := qpow_le_P x hx (s + 2)
          rw [← hq] at this
          have e : 4 * q ^ 2 * (((s : ℝ) + 1) * q ^ s) = 4 * ((s : ℝ) + 1) * q ^ (s + 2) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_left this (by positivity))
  rw [int_lin hn1] at h
  have a := sum2_range n hn (m + 1 + (m + 1))
  have e : ∑ s ∈ Finset.range (m + 1 + (m + 1)), 4 * ((s : ℝ) + 1) * muS n (s + 3)
      = 4 * ∑ s ∈ Finset.range (m + 1 + (m + 1)), ((s : ℝ) + 1) * muS n (s + 3) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
  rw [e] at h
  have e2 : (64 : ℝ) / (n : ℝ) ^ 2 = 4 * (16 / (n : ℝ) ^ 2) := by ring
  rw [e2]; linarith

theorem int_qG3 (n : ℕ) (hn : 1000 ≤ n) (m : ℕ) :
    ∫ x, (((∑ i, x i ^ 4) + ∑ i, x i ^ 6) * Gq m (∑ i, x i ^ 4)) ^ 3 ∂uniformSphere n ≤
      880 / (n : ℝ) ^ 3 := by
  have hn1 : 1 ≤ n := by omega
  have hPc := fun j => P_cont (n := n) j
  have h := int_le hn1
    (f := fun x : Fin n → ℝ => (((∑ i, x i ^ 4) + ∑ i, x i ^ 6) * Gq m (∑ i, x i ^ 4)) ^ 3)
    (g := fun x => ∑ s ∈ Finset.range (m + 1 + (m + 1 + (m + 1))),
      (8 * (((s : ℝ) + 1) * ((s : ℝ) + 2) / 2)) * P (s + 4) x)
    (by unfold Gq; fun_prop) (by fun_prop)
    (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := sphere_facts x hx
      obtain ⟨b1, b2⟩ := qG_bounds x hx m
      set q := ∑ i, x i ^ 4 with hq
      have hcu := Gq_cube_le m q h1
      calc ((q + ∑ i, x i ^ 6) * Gq m q) ^ 3 ≤ (2 * q * Gq m q) ^ 3 := by gcongr
        _ = 8 * q ^ 3 * Gq m q ^ 3 := by ring
        _ ≤ 8 * q ^ 3 * ∑ s ∈ Finset.range (m + 1 + (m + 1 + (m + 1))),
              (((s : ℝ) + 1) * ((s : ℝ) + 2) / 2) * q ^ s := by gcongr
        _ ≤ _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun s _ => ?_
          have := qpow_le_P x hx (s + 3)
          rw [← hq] at this
          have e : 8 * q ^ 3 * ((((s : ℝ) + 1) * ((s : ℝ) + 2) / 2) * q ^ s)
              = 8 * (((s : ℝ) + 1) * ((s : ℝ) + 2) / 2) * q ^ (s + 3) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_left this (by positivity))
  rw [int_lin hn1] at h
  have a := sum3_range n hn (m + 1 + (m + 1 + (m + 1)))
  have e : ∑ s ∈ Finset.range (m + 1 + (m + 1 + (m + 1))),
        8 * (((s : ℝ) + 1) * ((s : ℝ) + 2) / 2) * muS n (s + 4)
      = 8 * ∑ s ∈ Finset.range (m + 1 + (m + 1 + (m + 1))),
        (((s : ℝ) + 1) * ((s : ℝ) + 2) / 2) * muS n (s + 4) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
  rw [e] at h
  have e2 : (880 : ℝ) / (n : ℝ) ^ 3 = 8 * (110 / (n : ℝ) ^ 3) := by ring
  rw [e2]; linarith

end BstLean.Part81

#print axioms BstLean.Part81.int_powsum
#print axioms BstLean.Part81.int_sq_powsum
#print axioms BstLean.Part81.q_pow_le
#print axioms BstLean.Part81.muS_sum1
#print axioms BstLean.Part81.muS_sum2
#print axioms BstLean.Part81.muS_sum3
#print axioms BstLean.Part81.int_Gq
#print axioms BstLean.Part81.int_sq_Gq
#print axioms BstLean.Part81.int_qG1
#print axioms BstLean.Part81.int_qG2
#print axioms BstLean.Part81.int_qG3
