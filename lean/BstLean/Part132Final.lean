import BstLean.Part132B2
import BstLean.Part132Cross
import BstLean.Part132Num
import BstLean.Part132Cross2
import BstLean.Part132Quad

/-!
# Part 132, item 4: an explicit positive lower bound of the mean of `J`

Role: `delegations/statements/p132-spec.md`. Paper: `E J/S ≥ 0.31379` at `n = 4 096`
(`onW4-opus-prover.md` 2.7, `onW4c-cx.md` §5).

* `meanJ_lower`: for all widths and every `λ > 0`:
  `E J ≥ (4/n)·[3(κ^{∘6}(0) − eW − eA) − 2(κ(κ(0)) + β₂/√n + cF) − 1]` (first-order form).
* `meanJ_lower2`: the same with `(8/25)·(3/(2n) + eps4/2)` in the place of `β₂/√n`.
* **`meanJ132`**: at `r = 2` and the widths of the Focus, for every `n ≥ 4 096`:
  `E J ≥ (314/1000)·(4/n)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131

/-- **The mean of `J`, general widths**: for every `λ > 0`,
`E J ≥ (4/n)·[3(Q − eW n m_W λ − eA n m_A m_F) − 2(q + β₂/√n + cF m_F) − 1]`,
`Q = κ^{∘6}(0)`, `q = κ(κ(0))`. -/
theorem meanJ_lower {N mW n mA mF : ℕ} (hN : 1 ≤ N) (hmW : 1 ≤ mW) (hn : 1 ≤ n) (hmA : 1 ≤ mA)
    (hmF : 1 ≤ mF) {lam : ℝ} (hl : 0 < lam) :
    4 / (n : ℝ) * (3 * (kappa^[6] 0 - eW n mW lam - eA n mA mF) -
        2 * (kappa (kappa 0) + beta2 / √(n : ℝ) + cF mF) - 1) ≤
      ∫ t, Jall t ∂lawAll N mW n mA mF := by
  rw [meanJ_eq hn hN hmA hmF]
  have h1 := b2_lower (N := N) hN hmW hn hmA hmF hl
  have h2 := b11_upper (N := N) (mW := mW) hN hn hmA hmF
  linarith

/-- **The mean of `J`, general widths, second-order form** (the form to compare with the paper's
`j_n = 3(Q − e_b) − 2(q + 2.76/n + c₀/√m_F) − 1`): for every `λ > 0`,
`E J ≥ (4/n)·[3(Q − eW n m_W λ − eA n m_A m_F) − 2(q + cF m_F + (8/25)(3/(2n) + eps4 n m_A/2)) − 1]`.
-/
theorem meanJ_lower2 {N mW n mA mF : ℕ} (hN : 1 ≤ N) (hmW : 1 ≤ mW) (hn : 1 ≤ n) (hmA : 1 ≤ mA)
    (hmF : 1 ≤ mF) {lam : ℝ} (hl : 0 < lam) :
    4 / (n : ℝ) * (3 * (kappa^[6] 0 - eW n mW lam - eA n mA mF) -
        2 * (kappa (kappa 0) + cF mF + 8 / 25 * (3 / (2 * (n : ℝ)) + eps4 n mA / 2)) - 1) ≤
      ∫ t, Jall t ∂lawAll N mW n mA mF := by
  obtain ⟨b, hb⟩ := kk_quad
  rw [meanJ_eq hn hN hmA hmF]
  have h1 := b2_lower (N := N) hN hmW hn hmA hmF hl
  have h2 := b11_upper2 (N := N) (mW := mW) (b := b) (C := 8 / 25) hb (by norm_num) hN hn hmA hmF
  linarith

/-! ## The widths of the Focus for `n ≥ 4 096` -/

lemma mF_ge {n : ℕ} (hn : 4096 ≤ n) : 262144 ≤ mF n := by
  by_contra h
  have h0 : mF n ≤ 262143 := by omega
  rw [mF_le_iff] at h0
  have : 4096 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
  omega

lemma mW_ge {n : ℕ} (hn : 4096 ≤ n) : 4398046511104 ≤ mW n := by
  by_contra h
  have h0 : mW n ≤ 4398046511103 := by omega
  rw [mW_le_iff] at h0
  have : 4096 ^ 7 ≤ n ^ 7 := Nat.pow_le_pow_left hn 7
  omega

lemma eW_bound {n : ℕ} (hn : 4096 ≤ n) : eW n (mW n) 262144 ≤ 4155 / 1000000 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : (4398046511104 : ℝ) ≤ (mW n : ℝ) := by exact_mod_cast mW_ge hn
  have hk0 := (kappa_mem (t := 0) (by norm_num) (by norm_num))
  have h17 : 17 / (n : ℝ) ≤ 17 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have hd0 : 0 ≤ 5 / (mW n : ℝ) := by positivity
  have hd : 5 / (mW n : ℝ) ≤ 114 / 100000000000000 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hε : epsW (mW n) ≤ 23 / 10000000000000 := by
    unfold epsW; nlinarith
  have hε0 := epsW_nonneg (mW n)
  have hk : 10 / (mW n : ℝ) * kappa 0 ≤ 228 / 100000000000000 := by
    have e : 10 / (mW n : ℝ) = 2 * (5 / (mW n : ℝ)) := by ring
    rw [e]; nlinarith [hk0.1, hk0.2]
  unfold eW
  linarith

lemma eA_bound {n : ℕ} (hn : 4096 ≤ n) : eA n (mA n) (mF n) ≤ 5 / 10000 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hF : (262144 : ℝ) ≤ (mF n : ℝ) := by exact_mod_cast mF_ge hn
  have hA : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hq := kappa2_zero_le
  have hq0 : 0 ≤ kappa (kappa 0) := (kGood_kappa.comp_kappa).nonneg_on KGood.zero_mem
  have hk := kappa_zero_le
  have hk0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1
  have h4 : 4 / (n : ℝ) ≤ 4 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have h40 : 0 ≤ 4 / (n : ℝ) := by positivity
  have h20 : 20 / (mA n : ℝ) ≤ 20 / 4096 ^ 2 := by
    rw [hA]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have h10 : 10 / (mF n : ℝ) ≤ 10 / 262144 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hF
  have h100 : 0 ≤ 10 / (mF n : ℝ) := by positivity
  have t1 : 4 / (n : ℝ) * kappa (kappa 0) ≤ 4 / 4096 * (49376 / 100000) :=
    mul_le_mul h4 hq hq0 (by norm_num)
  have t3 : 10 / (mF n : ℝ) * kappa 0 ≤ 10 / 262144 * (31831 / 100000) :=
    mul_le_mul h10 hk hk0 (by norm_num)
  unfold eA
  norm_num at t1 t3 h20 ⊢
  linarith

lemma sqrt_n_ge {n : ℕ} (hn : 4096 ≤ n) : (64 : ℝ) ≤ √(n : ℝ) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have : √(4096 : ℝ) = 64 := by
    rw [show (4096 : ℝ) = 64 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← this]
  exact Real.sqrt_le_sqrt hx

lemma sqrt_mF_ge {n : ℕ} (hn : 4096 ≤ n) : (512 : ℝ) ≤ √(mF n : ℝ) := by
  have hF : (262144 : ℝ) ≤ (mF n : ℝ) := by exact_mod_cast mF_ge hn
  have : √(262144 : ℝ) = 512 := by
    rw [show (262144 : ℝ) = 512 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← this]
  exact Real.sqrt_le_sqrt hF

lemma beta_bound {n : ℕ} (hn : 4096 ≤ n) : beta2 / √(n : ℝ) ≤ 2590 / 1000000 := by
  have hs := sqrt_n_ge hn
  have hb : beta2 ≤ 165435 / 1000000 := by
    unfold beta2
    have := kappa2_zero_ge
    have := kappa_zero_le
    linarith
  have hb0 := beta2_nonneg
  calc beta2 / √(n : ℝ) ≤ (165435 / 1000000) / 64 :=
        div_le_div₀ (by norm_num) hb (by norm_num) hs
    _ ≤ 2590 / 1000000 := by norm_num

lemma cF_bound {n : ℕ} (hn : 4096 ≤ n) : cF (mF n) ≤ 7565 / 1000000 := by
  have hs := sqrt_mF_ge hn
  have h6 : √(6 : ℝ) ≤ 24495 / 10000 := by
    rw [show (24495 / 10000 : ℝ) = √((24495 / 10000) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h5 : √(5 : ℝ) ≤ 223607 / 100000 := by
    rw [show (223607 / 100000 : ℝ) = √((223607 / 100000) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hk := kappa_zero_le
  have hk0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  have h50 := Real.sqrt_nonneg (5 : ℝ)
  have hprod : √5 * kappa 0 ≤ 223607 / 100000 * (31831 / 100000) :=
    mul_le_mul h5 hk hk0 (by norm_num)
  unfold cF
  calc (√6 + 2 * √5 * kappa 0) / √(mF n : ℝ) ≤
        (24495 / 10000 + 2 * (223607 / 100000 * (31831 / 100000))) / 512 :=
        div_le_div₀ (by norm_num) (by nlinarith) (by norm_num) hs
    _ ≤ 7565 / 1000000 := by norm_num

lemma eps4_bound {n : ℕ} (hn : 4096 ≤ n) : eps4 n (mA n) ≤ 49 / 100000 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hA : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hd0 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  have hd : 5 / (mA n : ℝ) ≤ 3 / 10000000 := by
    rw [hA, div_le_iff₀ (by positivity)]; nlinarith
  have he0 : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have he : 2 / (n : ℝ) ≤ 2 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have h1 : (1 + 5 / (mA n : ℝ)) ^ 2 ≤ 1 + 7 / 10000000 := by nlinarith
  have h2 : (1 + 5 / (mA n : ℝ)) ^ 2 * (1 + 2 / (n : ℝ)) ≤ (1 + 7 / 10000000) * (1 + 2 / 4096) :=
    mul_le_mul h1 (by linarith) (by linarith) (by norm_num)
  unfold eps4
  norm_num at h2 ⊢
  linarith

/-- **`meanJ132`: the finite-width mean of `J` at the Focus** (`r = 2`, `m_W = ⌈n^{7/2}⌉`,
`m_A = n²`, `m_F = ⌈n^{3/2}⌉`). For every `n ≥ 4 096`: `E J ≥ (314/1000)·(4/n)`. The paper value is
`0.31379·(4/n)`. -/
theorem meanJ132 {n : ℕ} (hn : 4096 ≤ n) :
    314 / 1000 * (4 / (n : ℝ)) ≤ ∫ t, Jall t ∂lawAll (2 * n) (mW n) n (mA n) (mF n) := by
  have hn1 : 1 ≤ n := by omega
  have key := meanJ_lower2 (N := 2 * n) (mW := mW n) (n := n) (mA := mA n) (mF := mF n)
    (by omega) (one_le_mW hn1) hn1 (one_le_mA hn1) (one_le_mF hn1)
    (lam := 262144) (by norm_num)
  refine le_trans ?_ key
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 := eW_bound hn
  have h2 := eA_bound hn
  have h3 := eps4_bound hn
  have h4 := cF_bound hn
  have h5 := kappa6_zero_ge'
  have h6 := kappa2_zero_le
  have h7 : (3 : ℝ) / (2 * (n : ℝ)) ≤ 3 / (2 * 4096) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
          linarith)
  linarith

/-- The bound of `meanJ132` is positive. -/
theorem meanJ132_pos {n : ℕ} (hn : 4096 ≤ n) : (0 : ℝ) < 314 / 1000 * (4 / (n : ℝ)) := by
  have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  positivity

end BstLean.Part132

open BstLean.Part132 in
#print axioms meanJ_lower
open BstLean.Part132 in
#print axioms meanJ_lower2
open BstLean.Part132 in
#print axioms meanJ132
