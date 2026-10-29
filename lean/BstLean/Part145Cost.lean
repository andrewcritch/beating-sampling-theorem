import BstLean.Part144Cost

/-!
# Part 145, item 1: the operation count of the one-pass program for every `n ≥ 4096`

Role: `delegations/statements/p145-spec.md`, item 1 (`arithCost145`). Part 141 has the count
`2m² + m(6n + 4·LA n + 4) + LA n + 12 + k(…)` for every `n`, and Part 144 bounds it by
`2.000005·m²` only for `13225 ≤ n ≤ 16384` (the number of atoms `LA n` had a bound only for
`n ≤ 16384`). Here the number of atoms has a bound for every `n`.

* `clog_le_sqrt`: `⌈log₂ n⌉ ≤ ⌊√n⌋` for `n ≥ 36`.
* `LA_le`: `LA n ≤ 816n + 1` for every `n ≥ 4096` (the true order is `√n·log n`).
* `evalCost145`: `400·(5n + 2 + cost A + cost F) ≤ 801·n⁴` for `n ≥ 4096`.
* **`arithCost145`**: for every `n ≥ 4096`, with `k = 100n` cheap points:
  `n²·cost ≤ (2n² + 254)·m_W²`, that is `cost ≤ (2 + 254/n²)·m_W²`.
* `progCost145`: `cost ≤ 2.000002·m_W²` for every `n ≥ 13225`; `progCost145M`:
  `cost ≤ 2.000003·m_W²` for every `n ≥ 9216`; `progCost145_4096`: `≤ 2.000016·m_W²` for every
  `n ≥ 4096`.
* `progVsSample145`: the program costs at most `1.001` direct exact samples, every `n ≥ 4096`.
All counts are natural numbers of operations of the model `RProg` of Part 130.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open BstLean.Part130 BstLean.Part141 BstLean.Part144

/-- `(s + 1)² ≤ 2^s` for `s ≥ 6`. -/
lemma succ_sq_le_two_pow {s : ℕ} (hs : 6 ≤ s) : (s + 1) ^ 2 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have e : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [e]
    nlinarith

/-- `⌈log₂ n⌉ ≤ ⌊√n⌋` for `n ≥ 36`. -/
lemma clog_le_sqrt {n : ℕ} (hn : 36 ≤ n) : Nat.clog 2 n ≤ Nat.sqrt n := by
  have hs : 6 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  refine Nat.clog_le_of_le_pow ?_
  have h1 : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have h2 := succ_sq_le_two_pow hs
  have e : (Nat.sqrt n + 1) ^ 2 = (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by ring
  omega

/-- **The number of atoms for every `n`**: `LA n ≤ 816n + 1` for `n ≥ 4096`. -/
lemma LA_le {n : ℕ} (hn : 4096 ≤ n) : LA n ≤ 816 * n + 1 := by
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt n := ⟨_, rfl⟩
  have hs64 : 64 ≤ s := by rw [hs]; exact Nat.le_sqrt.mpr (by omega)
  have hss : s * s ≤ n := by rw [hs]; exact Nat.sqrt_le n
  have hlt : n < (s + 1) * (s + 1) := by rw [hs]; exact Nat.lt_succ_sqrt n
  have hR : RA n ≤ 19 + s := by
    have h := RA_le n
    have h2 := clog_le_sqrt (n := n) (by omega)
    omega
  have hH : hA n ≤ 200 * (s + 1) + 1 := by
    unfold hA qA
    have h1 : Nat.sqrt (4 * (10000 * n)) ≤ Nat.sqrt ((200 * (s + 1)) ^ 2) := by
      apply Nat.sqrt_le_sqrt
      have e : (200 * (s + 1)) ^ 2 = 40000 * ((s + 1) * (s + 1)) := by ring
      omega
    rw [Nat.sqrt_eq'] at h1
    omega
  have hR2 : RA n ≤ 2 * s := by omega
  have hH2 : hA n ≤ 204 * s := by omega
  have e : LA n = 2 * RA n * hA n + 1 := rfl
  rw [e]
  have h3 : 2 * RA n * hA n ≤ 2 * (2 * s) * (204 * s) := Nat.mul_le_mul (by omega) hH2
  have e3 : 2 * (2 * s) * (204 * s) = 816 * (s * s) := by ring
  omega

/-- `63·mF n ≤ n²` for `n ≥ 4096`. -/
lemma mF_le63 {n : ℕ} (hn : 4096 ≤ n) : 63 * mF n ≤ n ^ 2 := by
  have hF := BstLean.Part132.mF_ge hn
  have h1 : mF n ≤ n ^ 2 / 64 + 1 := by
    rw [mF_le_iff]
    have h2 : n ^ 2 < 64 * (n ^ 2 / 64 + 1) := by
      have := Nat.div_add_mod (n ^ 2) 64
      have := Nat.mod_lt (n ^ 2) (by norm_num : 0 < 64)
      omega
    have h3 : (n ^ 2) ^ 2 ≤ (64 * (n ^ 2 / 64 + 1)) ^ 2 := Nat.pow_le_pow_left h2.le 2
    have e3 : (64 * (n ^ 2 / 64 + 1)) ^ 2 = 4096 * (n ^ 2 / 64 + 1) ^ 2 := by ring
    have e4 : (n ^ 2) ^ 2 = n * n ^ 3 := by ring
    have h4 : 4096 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn
    omega
  have h5 : 64 * (n ^ 2 / 64) ≤ n ^ 2 := Nat.mul_div_le _ _
  omega

/-- One cheap point: `400·(5n + 2 + cost A + cost F) ≤ 801·n⁴` for `n ≥ 4096`. -/
lemma evalCost145 {n : ℕ} (hn : 4096 ≤ n) :
    400 * (5 * n + 2 + mlpCost n (mA n) n + mlpCost n (mF n) 1) ≤ 801 * n ^ 4 := by
  have hA := mlpCost_le n (mA n) n
  have hF := mlpCost_le n (mF n) 1
  have h63 := mF_le63 hn
  have a1 : mA n * n = n ^ 3 := by unfold mA; ring
  have a2 : mA n ^ 2 = n ^ 4 := by unfold mA; ring
  have a3 : n * mA n = n ^ 3 := by unfold mA; ring
  have a4 : mA n = n ^ 2 := rfl
  have f1 : 63 * (mF n * n) ≤ n ^ 3 := by
    have := Nat.mul_le_mul_right n h63
    have e : n ^ 2 * n = n ^ 3 := by ring
    have e2 : 63 * mF n * n = 63 * (mF n * n) := by ring
    omega
  have f2 : 3969 * mF n ^ 2 ≤ n ^ 4 := by
    have := Nat.pow_le_pow_left h63 2
    have e : (n ^ 2) ^ 2 = n ^ 4 := by ring
    have e2 : (63 * mF n) ^ 2 = 3969 * mF n ^ 2 := by ring
    omega
  have p2 : 4096 * n ≤ n ^ 2 := by
    have := Nat.mul_le_mul_right n hn
    have e : n * n = n ^ 2 := by ring
    omega
  have p3 : 4096 * n ^ 2 ≤ n ^ 3 := by
    have := Nat.mul_le_mul_right (n ^ 2) hn
    have e : n * n ^ 2 = n ^ 3 := by ring
    omega
  have p4 : 4096 * n ^ 3 ≤ n ^ 4 := by
    have := Nat.mul_le_mul_right (n ^ 3) hn
    have e : n * n ^ 3 = n ^ 4 := by ring
    omega
  omega

/-- `64·n³ ≤ mW n` for `n ≥ 4096`. -/
lemma mW_ge64 {n : ℕ} (hn : 4096 ≤ n) : 64 * n ^ 3 ≤ mW n := by
  have h := BstLean.Part136.mW_sq_ge n
  have h2 : (64 * n ^ 3) ^ 2 ≤ mW n ^ 2 := by
    have e : (64 * n ^ 3) ^ 2 = 4096 * n ^ 6 := by ring
    have e2 : n ^ 7 = n * n ^ 6 := by ring
    have := Nat.mul_le_mul_right (n ^ 6) hn
    omega
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h2

/-- **Item 1 (`arithCost145`): the operation count for every `n ≥ 4096`.** The arithmetic
one-pass program of Part 141 with `k = 100n` cheap points uses at most `(2 + 254/n²)·m_W²`
operations: `n²·cost ≤ (2n² + 254)·m_W²`. -/
theorem arithCost145 {n : ℕ} (hn : 4096 ≤ n) :
    n ^ 2 * (arithProg141 (100 * n) n).cost ≤ (2 * n ^ 2 + 254) * mW n ^ 2 := by
  obtain ⟨m, hm⟩ : ∃ m, m = mW n := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = (arithProg141 (100 * n) n).cost := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = 5 * n + 2 + mlpCost n (mA n) n + mlpCost n (mF n) 1 := ⟨_, rfl⟩
  have h : C ≤ 2 * m ^ 2 + m * (6 * n + 4 * LA n + 4) + LA n + 12 + 100 * n * E := by
    rw [hm, hC, hE]
    exact arithCost141_focus (100 * n) (n := n) (by omega)
  suffices hh : n ^ 2 * C ≤ (2 * n ^ 2 + 254) * m ^ 2 by
    rw [hC, hm] at hh
    exact hh
  have hL := LA_le hn
  have hEv := evalCost145 hn
  rw [← hE] at hEv
  have hm64 := mW_ge64 hn
  rw [← hm] at hm64
  have hm7 : n ^ 7 ≤ m ^ 2 := by rw [hm]; exact BstLean.Part136.mW_sq_ge n
  have p3 : 4096 * n ^ 2 ≤ n ^ 3 := by
    have := Nat.mul_le_mul_right (n ^ 2) hn
    have e : n * n ^ 2 = n ^ 3 := by ring
    omega
  have p2 : 4096 * n ≤ n ^ 2 := by
    have := Nat.mul_le_mul_right n hn
    have e : n * n = n ^ 2 := by ring
    omega
  -- the three small terms
  have T1 : n ^ 2 * (m * (6 * n + 4 * LA n + 4)) ≤ 52 * m ^ 2 := by
    have h1 : 6 * n + 4 * LA n + 4 ≤ 3271 * n := by omega
    have h2 : n ^ 2 * (3271 * n) ≤ 52 * m := by
      have e : n ^ 2 * (3271 * n) = 3271 * n ^ 3 := by ring
      omega
    calc n ^ 2 * (m * (6 * n + 4 * LA n + 4)) ≤ n ^ 2 * (m * (3271 * n)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ = m * (n ^ 2 * (3271 * n)) := by ring
      _ ≤ m * (52 * m) := Nat.mul_le_mul_left _ h2
      _ = 52 * m ^ 2 := by ring
  have T2 : n ^ 2 * (LA n + 12) ≤ m ^ 2 := by
    have h1 : LA n + 12 ≤ 817 * n := by omega
    have h2 : n ^ 2 * (817 * n) ≤ 13 * m := by
      have e : n ^ 2 * (817 * n) = 817 * n ^ 3 := by ring
      omega
    have h3 : 13 * m ≤ m ^ 2 := by
      have e : m ^ 2 = m * m := by ring
      rw [e]
      exact Nat.mul_le_mul_right m (by omega)
    exact (Nat.mul_le_mul_left _ h1).trans (h2.trans h3)
  have T3 : 4 * (n ^ 2 * (100 * n * E)) ≤ 801 * m ^ 2 := by
    have h1 : 4 * (n ^ 2 * (100 * n * E)) = n ^ 3 * (400 * E) := by ring
    have h2 : n ^ 3 * (400 * E) ≤ n ^ 3 * (801 * n ^ 4) := Nat.mul_le_mul_left _ hEv
    have h3 : n ^ 3 * (801 * n ^ 4) = 801 * n ^ 7 := by ring
    omega
  have hmain : n ^ 2 * C ≤ n ^ 2 * (2 * m ^ 2 + m * (6 * n + 4 * LA n + 4) + LA n + 12 +
      100 * n * E) := Nat.mul_le_mul_left _ h
  have e1 : n ^ 2 * (2 * m ^ 2 + m * (6 * n + 4 * LA n + 4) + LA n + 12 + 100 * n * E) =
      2 * n ^ 2 * m ^ 2 + n ^ 2 * (m * (6 * n + 4 * LA n + 4)) + n ^ 2 * (LA n + 12) +
        n ^ 2 * (100 * n * E) := by ring
  have e2 : (2 * n ^ 2 + 254) * m ^ 2 = 2 * n ^ 2 * m ^ 2 + 254 * m ^ 2 := by ring
  rw [e1] at hmain
  rw [e2]
  omega

/-- The count as a ratio, from a lower bound `n₀² ≥ D` of `n²`:
if `254·10⁶ ≤ c·n²` then `10⁶·cost ≤ (2·10⁶ + c)·m_W²`. -/
lemma progCost145_of {n : ℕ} (hn : 4096 ≤ n) {c : ℕ} (hc : 254 * 1000000 ≤ c * n ^ 2) :
    1000000 * (arithProg141 (100 * n) n).cost ≤ (2000000 + c) * mW n ^ 2 := by
  have h := arithCost145 hn
  have hn2 : 0 < n ^ 2 := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hn2
  calc n ^ 2 * (1000000 * (arithProg141 (100 * n) n).cost)
      = 1000000 * (n ^ 2 * (arithProg141 (100 * n) n).cost) := by ring
    _ ≤ 1000000 * ((2 * n ^ 2 + 254) * mW n ^ 2) := Nat.mul_le_mul_left _ h
    _ = (2000000 * n ^ 2 + 254 * 1000000) * mW n ^ 2 := by ring
    _ ≤ (2000000 * n ^ 2 + c * n ^ 2) * mW n ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.add_le_add_left hc _)
    _ = n ^ 2 * ((2000000 + c) * mW n ^ 2) := by ring

/-- **At most `2.000002·m_W²` operations for every `n ≥ 13225`** (`k = 100n` cheap points). -/
theorem progCost145 {n : ℕ} (hn : 13225 ≤ n) :
    1000000 * (arithProg141 (100 * n) n).cost ≤ 2000002 * mW n ^ 2 := by
  have h2 : 13225 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  exact progCost145_of (n := n) (by omega) (c := 2) (by omega)

/-- **At most `2.000003·m_W²` operations for every `n ≥ 9216`.** -/
theorem progCost145M {n : ℕ} (hn : 9216 ≤ n) :
    1000000 * (arithProg141 (100 * n) n).cost ≤ 2000003 * mW n ^ 2 := by
  have h2 : 9216 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  exact progCost145_of (n := n) (by omega) (c := 3) (by omega)

/-- **At most `2.000016·m_W²` operations for every `n ≥ 4096`** (the whole frontier interval
and above). -/
theorem progCost145_4096 {n : ℕ} (hn : 4096 ≤ n) :
    1000000 * (arithProg141 (100 * n) n).cost ≤ 2000016 * mW n ^ 2 := by
  have h2 : 4096 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  exact progCost145_of (n := n) hn (c := 16) (by omega)

/-- **The program costs at most `1.001` direct exact samples**, every `n ≥ 4096`. -/
theorem progVsSample145 {n : ℕ} (hn : 4096 ≤ n) :
    1000 * (arithProg141 (100 * n) n).cost ≤
      1001 * (sampleRProg 2 n (mW n) (mA n) (mF n)).cost := by
  have h := progCost145_4096 hn
  have hs := directSampleCost144 2 n (mW n) (mA n) (mF n)
  omega

end BstLean.Part145

open BstLean.Part145 in
#print axioms LA_le
open BstLean.Part145 in
#print axioms evalCost145
open BstLean.Part145 in
#print axioms arithCost145
open BstLean.Part145 in
#print axioms progCost145
open BstLean.Part145 in
#print axioms progCost145M
open BstLean.Part145 in
#print axioms progCost145_4096
open BstLean.Part145 in
#print axioms progVsSample145
