import BstLean.Part81Defs2
import BstLean.Part81KD

/-!
# Part 81 (UP): bounds for the complete homogeneous symmetric polynomials that are uniform in the
degree, and the resulting bounds for the kernel diagonal `κ(x,x)`.
-/

namespace BstLean.Part81.UP

open BstLean.Part53 (hS53)
open BstLean.Part81.KD
open Finset

variable {n : ℕ}

lemma one_sub_prod_le {ι : Type*} (T : Finset ι) (p : ι → ℝ)
    (hp : ∀ a ∈ T, 0 ≤ p a ∧ p a ≤ 1) : 1 - ∏ a ∈ T, p a ≤ ∑ a ∈ T, (1 - p a) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hT : ∀ b ∈ T, 0 ≤ p b ∧ p b ≤ 1 := fun b hb => hp b (Finset.mem_insert_of_mem hb)
    have h0 : 0 ≤ ∏ b ∈ T, p b := Finset.prod_nonneg fun b hb => (hT b hb).1
    have h1 : ∏ b ∈ T, p b ≤ 1 :=
      Finset.prod_le_one₀ (fun b hb => (hT b hb).1) (fun b hb => (hT b hb).2)
    have := ih hT
    obtain ⟨ha0, ha1⟩ := hp a (Finset.mem_insert_self a T)
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr h1)]

lemma fact_bd (m : ℕ) : 1 - 1 / (m.factorial : ℝ) ≤
    (if 2 ≤ m then (1 / 2 : ℝ) else 0) + (if 3 ≤ m then (1 / 2 : ℝ) else 0) := by
  by_cases h3 : 3 ≤ m
  · have h2 : 2 ≤ m := by omega
    have : (0 : ℝ) ≤ 1 / (m.factorial : ℝ) := by positivity
    simp only [h2, h3, ↓reduceIte]; linarith
  · have : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases this with rfl | rfl | rfl <;> norm_num [Nat.factorial]

lemma term_bd (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (j : ℕ) (s : Sym (Fin n) j) :
    ((j.factorial : ℝ) - s.1.countPerms) * (s.1.map z).prod ≤
      (j.factorial : ℝ) * ((1 / 2) * ∑ i, (if 2 ≤ s.1.count i then (s.1.map z).prod else 0)
        + (1 / 2) * ∑ i, (if 3 ≤ s.1.count i then (s.1.map z).prod else 0)) := by
  classical
  have hZ : 0 ≤ (s.1.map z).prod := prodNonneg53 z hz _
  set Z := (s.1.map z).prod with hZdef
  have hjf : (0 : ℝ) < j.factorial := by positivity
  set F : ℝ := ∏ i ∈ s.1.toFinset, ((s.1.count i).factorial : ℝ) with hF
  have hFpos : 0 < F := Finset.prod_pos fun i _ => by positivity
  have hspec : (s.1.countPerms : ℝ) * F = j.factorial := by
    have := cpSpec53 j s
    rw [hF]; exact_mod_cast this
  have hcp : (s.1.countPerms : ℝ) = j.factorial * (1 / F) := by
    field_simp; exact hspec
  have hinv : 1 / F = ∏ i ∈ s.1.toFinset, (1 / ((s.1.count i).factorial : ℝ)) := by
    rw [hF]; simp only [one_div]; rw [Finset.prod_inv_distrib]
  set w : Fin n → ℝ := fun i =>
    (if 2 ≤ s.1.count i then (1 / 2 : ℝ) else 0) + (if 3 ≤ s.1.count i then (1 / 2 : ℝ) else 0)
    with hw
  have hwn : ∀ i, 0 ≤ w i := fun i => by rw [hw]; positivity
  have h1 : 1 - 1 / F ≤ ∑ i, w i := by
    rw [hinv]
    calc 1 - ∏ i ∈ s.1.toFinset, (1 / ((s.1.count i).factorial : ℝ))
        ≤ ∑ i ∈ s.1.toFinset, (1 - 1 / ((s.1.count i).factorial : ℝ)) :=
          one_sub_prod_le _ _ (fun i _ => by
            constructor
            · positivity
            · rw [div_le_one (by positivity)]
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
      _ ≤ ∑ i ∈ s.1.toFinset, w i := Finset.sum_le_sum fun i _ => fact_bd _
      _ ≤ ∑ i, w i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hwn i)
  have h2 : (1 / 2) * ∑ i, (if 2 ≤ s.1.count i then Z else 0)
        + (1 / 2) * ∑ i, (if 3 ≤ s.1.count i then Z else 0) = (∑ i, w i) * Z := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hw]; dsimp only; split_ifs <;> ring
  rw [h2, hcp]
  have : ((j.factorial : ℝ) - j.factorial * (1 / F)) * Z = j.factorial * ((1 - 1 / F) * Z) := by
    ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hZ) hjf.le

/-- The sum of `z^s` over the `s` with at least `c` copies of `i`. -/
noncomputable def fS (z : Fin n → ℝ) (c j : ℕ) (i : Fin n) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Sym (Fin n) j)).filter (fun s => c ≤ s.1.count i), (s.1.map z).prod

lemma core (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) (j : ℕ) :
    hS53 z j - 1 / (j.factorial : ℝ) ≤ (1 / 2) * ∑ i, fS z 2 j i + (1 / 2) * ∑ i, fS z 3 j i := by
  classical
  have hid := multinomId53 z j
  rw [h1, one_pow] at hid
  have hjf : (0 : ℝ) < j.factorial := by positivity
  have hsum := Finset.sum_le_sum
    (fun s (_ : s ∈ (Finset.univ : Finset (Sym (Fin n) j))) => term_bd z hz j s)
  have hlhs : ∑ s : Sym (Fin n) j, ((j.factorial : ℝ) - s.1.countPerms) * (s.1.map z).prod =
      (j.factorial : ℝ) * hS53 z j - 1 := by
    rw [hid]; unfold hS53
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro s _; ring
  have hc : ∀ c : ℕ, ∑ s : Sym (Fin n) j, ∑ i, (if c ≤ s.1.count i then (s.1.map z).prod else 0)
      = ∑ i, fS z c j i := by
    intro c
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold fS; rw [Finset.sum_filter]
  have hrhs : ∑ s : Sym (Fin n) j, (j.factorial : ℝ) *
      ((1 / 2) * ∑ i, (if 2 ≤ s.1.count i then (s.1.map z).prod else 0)
        + (1 / 2) * ∑ i, (if 3 ≤ s.1.count i then (s.1.map z).prod else 0))
      = (j.factorial : ℝ) * ((1 / 2) * ∑ i, fS z 2 j i + (1 / 2) * ∑ i, fS z 3 j i) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hc, hc]
  rw [hlhs, hrhs] at hsum
  have h3 : hS53 z j - 1 / (j.factorial : ℝ) = ((j.factorial : ℝ) * hS53 z j - 1) / j.factorial := by
    field_simp
  rw [h3, div_le_iff₀ hjf]
  linarith

lemma fS_le (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (i : Fin n) : ∀ (c j : ℕ),
    fS z c j i ≤ z i ^ c * (if c ≤ j then hS53 z (j - c) else 0)
  | 0, j => by simp [fS, hS53]
  | c + 1, 0 => by
    classical
    have : (Finset.univ : Finset (Sym (Fin n) 0)).filter (fun s => c + 1 ≤ s.1.count i) = ∅ := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_le]
      have := Multiset.count_le_card i s.1
      rw [s.2] at this
      omega
    unfold fS
    rw [this, Finset.sum_empty]; simp
  | c + 1, j + 1 => by
    classical
    have ih := fS_le z hz i c j
    have himg : (Finset.univ : Finset (Sym (Fin n) (j + 1))).filter (fun s => c + 1 ≤ s.1.count i)
        = ((Finset.univ : Finset (Sym (Fin n) j)).filter (fun s => c ≤ s.1.count i)).image
            (fun s' => i ::ₛ s') := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hc
        have h1 : i ∈ s := Multiset.count_pos.mp (by omega)
        refine ⟨s.erase i h1, ?_, Sym.cons_erase h1⟩
        show c ≤ Multiset.count i ((s.erase i h1 : Sym (Fin n) j) : Multiset (Fin n))
        rw [Sym.coe_erase, Multiset.count_erase_self]
        exact Nat.le_sub_one_of_lt hc
      · rintro ⟨s', hs', rfl⟩
        show c + 1 ≤ Multiset.count i (((i ::ₛ s') : Sym (Fin n) (j + 1)) : Multiset (Fin n))
        rw [Sym.coe_cons, Multiset.count_cons_self]
        exact Nat.succ_le_succ hs'
    have hinj : Function.Injective (fun s' : Sym (Fin n) j => i ::ₛ s') :=
      fun a b h => (Sym.cons_inj_right _ _ _).mp h
    have hstep : fS z (c + 1) (j + 1) i = z i * fS z c j i := by
      unfold fS
      rw [himg, Finset.sum_image (fun a _ b _ h => hinj h), Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      show ((((i ::ₛ s') : Sym (Fin n) (j + 1)) : Multiset (Fin n)).map z).prod = _
      rw [Sym.coe_cons, Multiset.map_cons, Multiset.prod_cons]
      rfl
    rw [hstep]
    calc z i * fS z c j i ≤ z i * (z i ^ c * (if c ≤ j then hS53 z (j - c) else 0)) :=
          mul_le_mul_of_nonneg_left ih (hz i)
      _ = _ := by
          simp only [Nat.add_le_add_iff_right, Nat.add_sub_add_right]; ring

lemma hS_nonneg (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (j : ℕ) : 0 ≤ hS53 z j :=
  Finset.sum_nonneg fun _ _ => prodNonneg53 z hz _

lemma fS_anti (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (j : ℕ) (i : Fin n) : fS z 3 j i ≤ fS z 2 j i := by
  classical
  unfold fS
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    omega
  · intro s _ _; exact prodNonneg53 z hz _

lemma sum_fS_le (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (c j : ℕ) :
    ∑ i, fS z c j i ≤ (∑ i, z i ^ c) * (if c ≤ j then hS53 z (j - c) else 0) := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => fS_le z hz i c j

/-- (L1), every degree: the shifted term is `0` below degree 2. -/
lemma gen1 (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) (j : ℕ) :
    hS53 z j ≤ 1 / (j.factorial : ℝ) + (∑ i, z i ^ 2) * (if 2 ≤ j then hS53 z (j - 2) else 0) := by
  have hc := core z hz h1 j
  have h2 := sum_fS_le z hz 2 j
  have h3 : ∑ i, fS z 3 j i ≤ ∑ i, fS z 2 j i := Finset.sum_le_sum fun i _ => fS_anti z hz j i
  linarith

/-- (L2), every degree. -/
lemma gen2 (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) (j : ℕ) :
    hS53 z j ≤ 1 / (j.factorial : ℝ)
      + (∑ i, z i ^ 2) / 2 * (if 2 ≤ j then hS53 z (j - 2) else 0)
      + (∑ i, z i ^ 3) / 2 * (if 3 ≤ j then hS53 z (j - 3) else 0) := by
  have hc := core z hz h1 j
  have h2 := sum_fS_le z hz 2 j
  have h3 := sum_fS_le z hz 3 j
  linarith

lemma shift_sum (f : ℕ → ℝ) (c : ℕ) : ∀ N : ℕ,
    ∑ j ∈ Finset.range N, (if c ≤ j then f (j - c) else 0) = ∑ i ∈ Finset.range (N - c), f i
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, shift_sum f c N]
    by_cases h : c ≤ N
    · simp only [h, ↓reduceIte]; rw [Nat.succ_sub h, Finset.sum_range_succ]
    · simp only [h, ↓reduceIte]
      have : N + 1 - c = N - c := by omega
      rw [this, add_zero]

lemma shift_sum_le (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (c N : ℕ) :
    ∑ j ∈ Finset.range N, (if c ≤ j then f (j - c) else 0) ≤ ∑ i ∈ Finset.range N, f i := by
  rw [shift_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.sub_le _ _)) (fun i _ _ => hf i)

lemma sum_inv_fact_le (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), 1 / (j.factorial : ℝ) ≤ 2719 / 1000 := by
  rw [Finset.sum_range_succ', ← eD_eq]
  have := eD_le m
  norm_num
  linarith

lemma Gq_succ (m : ℕ) (q : ℝ) : Gq (m + 1) q = 1 + q * Gq m q := by
  unfold Gq
  rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

lemma Gq_nonneg (m : ℕ) (q : ℝ) (hq : 0 ≤ q) : 0 ≤ Gq m q :=
  Finset.sum_nonneg fun _ _ => pow_nonneg hq _

lemma sum_le_aux (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) : ∀ m : ℕ,
    ∑ j ∈ Finset.range (m + 1), hS53 z j ≤ 2719 / 1000 * Gq (m / 2) (∑ i, z i ^ 2)
  | 0 => by simp [Gq, hSZero53]; norm_num
  | 1 => by
    have h0 := hSBounds53 z hz h1 0
    have h1' := hSLeOne53 z hz h1 1
    have h0' := hSLeOne53 z hz h1 0
    simp [Gq, Finset.sum_range_succ]
    linarith
  | m + 2 => by
    have ih := sum_le_aux z hz h1 m
    have hq : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hG : (m + 2) / 2 = m / 2 + 1 := by omega
    rw [hG, Gq_succ]
    have hs := Finset.sum_le_sum
      (fun j (_ : j ∈ Finset.range (m + 2 + 1)) => gen1 z hz h1 j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, shift_sum] at hs
    have hE := sum_inv_fact_le (m + 2)
    have : m + 2 + 1 - 2 = m + 1 := by omega
    rw [this] at hs
    nlinarith [mul_le_mul_of_nonneg_left ih hq]

end BstLean.Part81.UP

namespace BstLean.Part81

open BstLean.Part53 (hS53)
open BstLean.Part81.KD BstLean.Part81.UP
open Finset

/-- (L1). -/
theorem hS_step1 (n j : ℕ) (hj : 2 ≤ j) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) :
    hS53 z j ≤ 1 / (j.factorial : ℝ) + (∑ i, z i ^ 2) * hS53 z (j - 2) := by
  have := gen1 z hz h1 j
  simpa only [hj, ↓reduceIte] using this

/-- (L2). -/
theorem hS_step2 (n j : ℕ) (hj : 3 ≤ j) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) :
    hS53 z j ≤ 1 / (j.factorial : ℝ) + (∑ i, z i ^ 2) / 2 * hS53 z (j - 2)
      + (∑ i, z i ^ 3) / 2 * hS53 z (j - 3) := by
  have := gen2 z hz h1 j
  have hj2 : 2 ≤ j := by omega
  simpa only [hj, hj2, ↓reduceIte] using this

/-- (L2) at degree 2 (upper half of `h_2 = 1/2 + q/2`). -/
theorem hS_two_le (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) :
    hS53 z 2 ≤ 1 / 2 + (∑ i, z i ^ 2) / 2 := by
  have := gen2 z hz h1 2
  simp [hSZero53] at this
  linarith

/-- (U1). -/
theorem hS_sum_le (n m : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) :
    ∑ j ∈ Finset.range (m + 1), BstLean.Part53.hS53 z j
      ≤ 2719 / 1000 * Gq (m / 2) (∑ i, z i ^ 2) :=
  sum_le_aux z hz h1 m

/-- (U2), before the bound of the partial sum. -/
theorem hS_delta_le (n d : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) :
    ∑ j ∈ Finset.range d, (hS53 z (j + 1) - 1 / ((j + 1).factorial : ℝ))
      ≤ ((∑ i, z i ^ 2) + ∑ i, z i ^ 3) / 2 * ∑ j ∈ Finset.range (d + 1), hS53 z j := by
  have hq : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hr : 0 ≤ ∑ i, z i ^ 3 := Finset.sum_nonneg fun i _ => pow_nonneg (hz i) _
  have e : ∑ j ∈ Finset.range d, (hS53 z (j + 1) - 1 / ((j + 1).factorial : ℝ))
      = ∑ j ∈ Finset.range (d + 1), (hS53 z j - 1 / (j.factorial : ℝ)) := by
    rw [Finset.sum_range_succ' _ d]; simp [hSZero53]
  rw [e]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (d + 1)) =>
    sub_le_iff_le_add'.mpr (by have := gen2 z hz h1 j; linarith :
      hS53 z j ≤ 1 / (j.factorial : ℝ) +
        ((∑ i, z i ^ 2) / 2 * (if 2 ≤ j then hS53 z (j - 2) else 0)
          + (∑ i, z i ^ 3) / 2 * (if 3 ≤ j then hS53 z (j - 3) else 0))))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have s2 := shift_sum_le (hS53 z) (hS_nonneg z hz) 2 (d + 1)
  have s3 := shift_sum_le (hS53 z) (hS_nonneg z hz) 3 (d + 1)
  nlinarith [mul_le_mul_of_nonneg_left s2 (by positivity : (0:ℝ) ≤ (∑ i, z i ^ 2) / 2), mul_le_mul_of_nonneg_left s3 (by positivity : (0:ℝ) ≤ (∑ i, z i ^ 3) / 2)]

theorem kap_diag_le_G (n d : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    1 + kap d x x ≤ 2719 / 1000 * Gq (d / 2) (∑ i, x i ^ 4) := by
  have h := hS_sum_le n d (fun i => x i ^ 2) (fun i => sq_nonneg _) hx
  rw [q4_eq, Finset.sum_range_succ', hSZero53, add_comm, ← kap_diag_hS] at h
  exact h

theorem kap_delta_le (n d : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    kap d x x - eD d ≤
      2719 / 2000 * ((∑ i, x i ^ 4) + ∑ i, x i ^ 6) * Gq (d / 2) (∑ i, x i ^ 4) := by
  have h := hS_delta_le n d (fun i => x i ^ 2) (fun i => sq_nonneg _) hx
  have hS := hS_sum_le n d (fun i => x i ^ 2) (fun i => sq_nonneg _) hx
  have e6 : ∑ i, (fun i => x i ^ 2) i ^ 3 = ∑ i, x i ^ 6 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [q4_eq] at hS
  rw [q4_eq, e6, Finset.sum_sub_distrib, ← kap_diag_hS, ← eD_eq] at h
  have hq : 0 ≤ ∑ i, x i ^ 4 := Finset.sum_nonneg fun i _ => by positivity
  have hr : 0 ≤ ∑ i, x i ^ 6 := Finset.sum_nonneg fun i _ => by positivity
  have := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ ((∑ i, x i ^ 4) + ∑ i, x i ^ 6) / 2)
  linarith

end BstLean.Part81

#print axioms BstLean.Part81.hS_step1
#print axioms BstLean.Part81.hS_step2
#print axioms BstLean.Part81.hS_two_le
#print axioms BstLean.Part81.hS_sum_le
#print axioms BstLean.Part81.hS_delta_le
#print axioms BstLean.Part81.kap_diag_le_G
#print axioms BstLean.Part81.kap_delta_le
