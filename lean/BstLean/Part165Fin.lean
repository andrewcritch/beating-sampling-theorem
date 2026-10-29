import BstLean.Part165Root

/-!
# Part 165 (file `Fin`): the end theorem with the mass AND the root sum discharged

No proof is left open; no `native_decide` or `axiom` is used.

* `cLS4_le`, `cLS6_le`, `cLS12_le`: decimal bounds of the rotation constants `c_q`.
* `kLSs_le`: `c_q(n − 1 − 2q)^{−1/2} ≤ K·√(2/n)` for `n ≥ 23 000`.
* `lat_fields`: the fields of `latMomOfPsi12e` at `C_λ = 5.1`, `C_σ = 3.26·γ_A`, `E = E0 n`,
  `β_low = betaM n 0.43` satisfy the bounds of `root_core`.
* **`rootFL_fixed`**: `rootFL ≤ 0.002159` at `w_l = 22γ_A`, `w_s = 17.5γ_A^{3/2}`, `η = 10⁻⁴`,
  `σ_l = 0.43√γ_A`, `C_A = CAn n` (every `n ≥ 23 000`).
* **`classifier_paper_free23_root`**: `classifier_paper_free23_mass40` with the root-sum
  hypothesis REMOVED. What remains: the two order-12 certificates with the fixed constants
  `C_λ = 5.1`, `C_σ = 3.26·γ_A`, and `BIAS_hyp` at the fixed split data.
-/

namespace BstLean.Part165

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part161 (muI lamX sigX BIAS_hyp)
open BstLean.Part162 (sgA psiA rootFL latMomOfPsi12e eps0 dPaper cLS kLSs gmom gmom_even LatMom)
open BstLean.Part164 (goodA hE8_of_good CAn E0 E0_nonneg CAn_le E0_le)

variable {n : ℕ}

lemma pi_half_le : π / 2 ≤ 15708 / 10000 := by have := Real.pi_lt_d4; linarith

lemma cLS_le_of {q : ℕ} (hq : 1 ≤ q) {G y : ℝ} (hG : gmom (2 * q) = G) (hG0 : 0 ≤ G)
    (hy : 0 ≤ y) (h : G ≤ y ^ (2 * q)) : cLS q ≤ 15708 / 10000 * y := by
  unfold cLS
  rw [hG]
  have h1 : G ^ (((2 * q : ℕ) : ℝ)⁻¹) ≤ y := by
    rw [Real.rpow_inv_le_iff_of_pos hG0 hy (by positivity), Real.rpow_natCast]
    exact h
  have h2 : 0 ≤ G ^ (((2 * q : ℕ) : ℝ)⁻¹) := by positivity
  exact mul_le_mul pi_half_le h1 h2 (by norm_num)

lemma cLS4_le : cLS 4 ≤ 28106 / 10000 := by
  have hG : gmom (2 * 4) = 105 := by rw [gmom_even]; norm_num [Finset.prod_range_succ]
  exact (cLS_le_of (y := 17892 / 10000) (by norm_num) hG (by norm_num) (by norm_num)
    (by norm_num)).trans (by norm_num)

lemma cLS6_le : cLS 6 ≤ 33953 / 10000 := by
  have hG : gmom (2 * 6) = 10395 := by rw [gmom_even]; norm_num [Finset.prod_range_succ]
  exact (cLS_le_of (y := 21615 / 10000) (by norm_num) hG (by norm_num) (by norm_num)
    (by norm_num)).trans (by norm_num)

lemma cLS12_le : cLS 12 ≤ 47348 / 10000 := by
  have hG : gmom (2 * 12) = 316234143225 := by rw [gmom_even]; norm_num [Finset.prod_range_succ]
  exact (cLS_le_of (y := 30142 / 10000) (by norm_num) hG (by norm_num) (by norm_num)
    (by norm_num)).trans (by norm_num)

lemma cLS_nonneg' (q : ℕ) : 0 ≤ cLS q := BstLean.Part162.cLS_nonneg q

/-- `kLSs n q ≤ K·√(2/n)` from `c_q ≤ C` and `C² ≤ K²(2 − (1 + 2q)·2/23000)`, `n ≥ 23 000`. -/
lemma kLSs_le (hn : 23000 ≤ n) {q : ℕ} (hq : q ≤ 12) {C K : ℝ} (hC : cLS q ≤ C) (hK0 : 0 ≤ K)
    (hCK : C ^ 2 ≤ K ^ 2 * (2 - (1 + 2 * q) * (2 / 23000))) :
    kLSs n q ≤ K * √(2 / (n : ℝ)) := by
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hn0 : (0 : ℝ) < n := by linarith
  have hd : 0 < (n : ℝ) - 1 - 2 * q := by linarith
  have hc0 := cLS_nonneg' q
  have hC0 : 0 ≤ C := hc0.trans hC
  unfold kLSs
  rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  rw [← Real.sqrt_sq hc0, ← Real.sqrt_mul (sq_nonneg _), ← Real.sqrt_sq hK0,
    ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  have h1 : cLS q ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ hc0 hC 2
  rw [mul_div_assoc', le_div_iff₀ hn0, ← div_eq_mul_inv, div_mul_eq_mul_div, div_le_iff₀ hd]
  have h2 : C ^ 2 * n ≤ K ^ 2 * 2 * ((n : ℝ) - 1 - 2 * q) := by
    have h3 : (2 - (1 + 2 * q) * (2 / 23000)) * n ≤ 2 * ((n : ℝ) - 1 - 2 * q) := by nlinarith
    calc C ^ 2 * n ≤ K ^ 2 * (2 - (1 + 2 * q) * (2 / 23000)) * n :=
          mul_le_mul_of_nonneg_right hCK hn0.le
      _ = K ^ 2 * ((2 - (1 + 2 * q) * (2 / 23000)) * n) := by ring
      _ ≤ K ^ 2 * (2 * ((n : ℝ) - 1 - 2 * q)) := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = K ^ 2 * 2 * ((n : ℝ) - 1 - 2 * q) := by ring
  nlinarith [mul_le_mul_of_nonneg_right h1 hn0.le]

/-- **The root sum at the fixed constants, for every `n ≥ 23 000`**: with `C_λ = 5.1`,
`C_σ = 3.26·γ_A`, `E = E0 n`, `β_low = betaM n 0.43`, `w_l = 22γ_A`, `w_s = 17.5γ_A^{3/2}`,
`η = 10⁻⁴`, `σ_l = 0.43√γ_A` and `C_A = CAn n`: `rootFL ≤ 0.002159`. -/
theorem rootFL_fixed (hn : 23000 ≤ n) {sd : ℝ} (hsd : 43 / 100 ≤ sd)
    (hβ : betaM n sd ≤ 3 / 10 ^ 14) (D : Design n) (c : Ret n)
    (hCL : (0 : ℝ) < 51 / 10) (hCS : (0 : ℝ) < 326 / 100 * (2 / n))
    (hL12 : ∫ a, ∫ v, psiA (lamX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12)
    (hS12 : ∫ a, ∫ v, psiA (sigX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (326 / 100 * (2 / n) / n) ^ 12)
    (hE8 : ∫ a, ∫ v, sgA D c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ E0 n ^ 8)
    (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA D c a v < √(2 / (n : ℝ)) * sd}
      ∂muI n ≤ betaM n sd) :
    rootFL (22 * √(2 / (n : ℝ)) ^ 2) (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (1 / 10000)
      (CAn n) (latMomOfPsi12e (by omega) D c hCL hCS (E0_nonneg n) (betaM_nonneg n sd)
        hL12 hS12 hE8 hmass) ≤ 2159 / 10 ^ 6 := by
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set g := √(2 / (n : ℝ)) with hgdef
  have hg2 : g ^ 2 = 2 / n := Real.sq_sqrt (by positivity)
  have hg : 0 < g := Real.sqrt_pos.mpr (by positivity)
  have hgn : (n : ℝ) * g ^ 2 = 2 := by rw [hg2]; field_simp
  have hg0 : g ^ 2 ≤ 2 / 23000 := by
    rw [hg2]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  set P := latMomOfPsi12e (by omega) D c hCL hCS (E0_nonneg n) (betaM_nonneg n sd)
    hL12 hS12 hE8 hmass with hP
  -- the two square roots
  have hCSn : √(326 / 100 * (2 / (n : ℝ)) / n) = √(163 / 100) * g ^ 2 := by
    rw [hg2, show 326 / 100 * (2 / (n : ℝ)) / n = 163 / 100 * (2 / n) ^ 2 by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  have hCLn : √(51 / 10 / (n : ℝ)) = √(255 / 100) * g := by
    rw [hgdef, ← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have hs1 : √(163 / 100 : ℝ) ≤ 1276715 / 1000000 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs2 : √(255 / 100 : ℝ) ≤ 1596872 / 1000000 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs10 : 0 ≤ √(163 / 100 : ℝ) := Real.sqrt_nonneg _
  have hs20 : 0 ≤ √(255 / 100 : ℝ) := Real.sqrt_nonneg _
  -- the factors `kLSs`
  have hk4 : kLSs n 4 ≤ 198779 / 100000 * g :=
    kLSs_le hn (by norm_num) cLS4_le (by norm_num) (by norm_num)
  have hk6 : kLSs n 6 ≤ 240152 / 100000 * g :=
    kLSs_le hn (by norm_num) cLS6_le (by norm_num) (by norm_num)
  have hk12 : kLSs n 12 ≤ 334984 / 100000 * g :=
    kLSs_le hn (by norm_num) cLS12_le (by norm_num) (by norm_num)
  have hk40 : 0 ≤ kLSs n 4 := (BstLean.Part162.kLSs_pos' (by omega) (by norm_num) (by norm_num)).le
  have hk60 : 0 ≤ kLSs n 6 := (BstLean.Part162.kLSs_pos' (by omega) (by norm_num) (by norm_num)).le
  have hk120 : 0 ≤ kLSs n 12 :=
    (BstLean.Part162.kLSs_pos' (by omega) (by norm_num) (by norm_num)).le
  have hu : 0 ≤ g ^ 2 := sq_nonneg g
  -- the fields
  have fS : ∀ {k K : ℝ}, 0 ≤ k → k ≤ K * g → ∀ {M : ℝ}, K * (1276715 / 1000000) ≤ M →
      k * √(326 / 100 * (2 / (n : ℝ)) / n) ≤ M * (g ^ 2 * g) := by
    intro k K hk0 hk M hM
    rw [hCSn]
    have hK0 : 0 ≤ K := by
      by_contra h
      have : K * g < 0 := mul_neg_of_neg_of_pos (not_le.mp h) hg
      linarith
    calc k * (√(163 / 100) * g ^ 2) ≤ (K * g) * (1276715 / 1000000 * g ^ 2) := by gcongr
      _ = K * (1276715 / 1000000) * (g ^ 2 * g) := by ring
      _ ≤ M * (g ^ 2 * g) := by gcongr
  have fL : ∀ {k K : ℝ}, 0 ≤ k → k ≤ K * g → ∀ {M : ℝ}, K * (1596872 / 1000000) ≤ M →
      k * √(51 / 10 / (n : ℝ)) ≤ M * g ^ 2 := by
    intro k K hk0 hk M hM
    rw [hCLn]
    have hK0 : 0 ≤ K := by
      by_contra h
      have : K * g < 0 := mul_neg_of_neg_of_pos (not_le.mp h) hg
      linarith
    calc k * (√(255 / 100) * g) ≤ (K * g) * (1596872 / 1000000 * g) := by gcongr
      _ = K * (1596872 / 1000000) * g ^ 2 := by ring
      _ ≤ M * g ^ 2 := by gcongr
  have hts8 : P.ts8 ≤ 25379 / 10000 * (g ^ 2 * g) := fS hk40 hk4 (by norm_num)
  have hts12 : P.ts12 ≤ 30661 / 10000 * (g ^ 2 * g) := fS hk60 hk6 (by norm_num)
  have htsq : P.tsq ≤ 42768 / 10000 * (g ^ 2 * g) := fS hk120 hk12 (by norm_num)
  have htl8 : P.tl8 ≤ 31743 / 10000 * g ^ 2 := fL hk40 hk4 (by norm_num)
  have htl12 : P.tl12 ≤ 38350 / 10000 * g ^ 2 := fL hk60 hk6 (by norm_num)
  have htlq : P.tlq ≤ 53493 / 10000 * g ^ 2 := fL hk120 hk12 (by norm_num)
  have hVs : P.Vs ≤ 81508 / 100000 * (g ^ 2) ^ 3 := by
    change 326 / 100 * (2 / (n : ℝ)) / n / ((n : ℝ) - 2) ≤ _
    rw [hg2]
    have hd : (0 : ℝ) < n - 2 := by linarith
    rw [div_le_iff₀ hd]
    have e : 81508 / 100000 * (2 / (n : ℝ)) ^ 3 * (n - 2) = 652064 / 100000 * (n - 2) / n ^ 3 := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : 326 / 100 * (2 / (n : ℝ)) / n * n ^ 3 = 652 / 100 * n := by field_simp; ring
    rw [e2]
    nlinarith
  have hVl : P.Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2 := by
    change 51 / 10 / (n : ℝ) / ((n : ℝ) - 2) ≤ _
    rw [hg2]
    have hd : (0 : ℝ) < n - 2 := by linarith
    rw [div_le_iff₀ hd]
    have e : 127512 / 100000 * (2 / (n : ℝ)) ^ 2 * (n - 2) = 510048 / 100000 * (n - 2) / n ^ 2 := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : 51 / 10 / (n : ℝ) * n ^ 2 = 51 / 10 * n := by field_simp
    rw [e2]
    nlinarith
  have hVS : P.VS ≤ 4247 / 10 * (g ^ 2) ^ 4 := by
    change 4 * (kLSs n 4 * √(326 / 100 * (2 / (n : ℝ)) / n)) ^ 2 * E0 n ^ 2 ≤ _
    have h1 := fS hk40 hk4 (M := 25379 / 10000) (by norm_num)
    have h10 : 0 ≤ kLSs n 4 * √(326 / 100 * (2 / (n : ℝ)) / n) := by positivity
    have h2 := E0_le hn
    rw [← hgdef] at h2
    calc 4 * (kLSs n 4 * √(326 / 100 * (2 / (n : ℝ)) / n)) ^ 2 * E0 n ^ 2
        ≤ 4 * (25379 / 10000 * (g ^ 2 * g)) ^ 2 * (406 / 100 * g) ^ 2 := by
          gcongr
          exact E0_nonneg n
      _ = 4 * (25379 / 10000) ^ 2 * (406 / 100) ^ 2 * (g ^ 2) ^ 4 := by ring
      _ ≤ 4247 / 10 * (g ^ 2) ^ 4 := by gcongr; norm_num
  have hβ' : P.βlow ≤ 3 / 10 ^ 14 := hβ
  have hCA := CAn_le hn
  have hCA0 : 0 ≤ CAn n := by unfold CAn BstLean.Part164.chiUp; positivity
  exact root_core hg hgn hg0 hsd hCA0 hCA P.hVs0 hVs P.hVl0 hVl P.hVS0 hVS P.hts8.le hts8 P.htl8.le
    htl8 P.hts12.le hts12 P.htl12.le htl12 P.htlq htlq P.htsq htsq P.hβl hβ'

/-- `ε₀ < 1` at the fixed constants. -/
lemma eps0_fixed_lt (hn : 23000 ≤ n) {sd : ℝ} (hsd : 43 / 100 ≤ sd) :
    eps0 (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * sd) < 1 := by
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
  have hg : 0 < √(2 / (n : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hg0 : √(2 / (n : ℝ)) ^ 2 ≤ 2 / 23000 := by
    rw [Real.sq_sqrt (by positivity)]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have := (rc_eps hg hg0 hsd).2.2
  linarith

/-- **The mass bound at the floor `sd = 0.4691`** (`d_low = 0.22005 ≥ 0.22`, the paper's floor):
`betaM n 0.4691 ≤ 3·10⁻¹⁴` for `n ≥ 80 000`. -/
theorem betaM_4691 (hn : 80000 ≤ n) : betaM n (4691 / 10000) ≤ 3 / 10 ^ 14 := by
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold betaM s0
  rw [gmom_40]
  have h1 : (π / 2) ^ 40 ≤ (15708 / 10000 : ℝ) ^ 40 := pow_le_pow_left₀ (by positivity) pi_half_le 40
  have h2 : 706 / 1000 / ((n : ℝ) * (5087 / 10000 - 4691 / 10000) ^ 2) ≤
      706 / 1000 / ((80000 : ℝ) * (5087 / 10000 - 4691 / 10000) ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right hnR (by norm_num))
  have h3 := pow_le_pow_left₀ (by positivity) h2 20
  calc (π / 2) ^ 40 * 319830986772877770815625 *
        (706 / 1000 / ((n : ℝ) * (5087 / 10000 - 4691 / 10000) ^ 2)) ^ 20
      ≤ (15708 / 10000 : ℝ) ^ 40 * 319830986772877770815625 *
        (706 / 1000 / ((80000 : ℝ) * (5087 / 10000 - 4691 / 10000) ^ 2)) ^ 20 :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by norm_num)) h3 (by positivity)
          (by positivity)
    _ ≤ 3 / 10 ^ 14 := by norm_num

/-- **The free-event classifier theorem with the mass below the floor AND the root sum
discharged, for a floor `sd`.** For `n ≥ 23 000`, `0.43 ≤ sd < s0` and `betaM n sd ≤ 3·10⁻¹⁴`:
IF `E_A` is a measurable event with `Pr(HP n ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ) ≤ δ_A ≤ roomC`, and for
every `c` in the good set `goodC` the two order-12 certificates hold with `C_λ = 5.1` and
`C_σ = 3.26·γ_A` and `BIAS_hyp … 0.004295` holds for the split data `dPaper` at
`w_l = 22γ_A`, `w_s = 17.5γ_A^{3/2}`, `σ_l = sd·√γ_A`, `η = 10⁻⁴`, THEN the classifier program
succeeds with probability `≥ 99/100` for the actual random networks. -/
theorem classifier_paper_root_gen (hn : 23000 ≤ n) {sd : ℝ} (hsd : 43 / 100 ≤ sd)
    (hsd' : sd < s0) (hβ : betaM n sd ≤ 3 / 10 ^ 14) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC)
    (hM : ∀ c ∈ goodC n (paperDesign n fT wT hf hw) EA,
      (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
      (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) ∧
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * sd)
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsd0 : 0 < sd := lt_of_lt_of_le (by norm_num) hsd
  refine classifier_paper_free23_mass40 hn fT wT hf hw t hEA hA hroom fun c hc => ?_
  obtain ⟨hL12, hS12, hbias⟩ := hM c hc
  have hCS : (0 : ℝ) < 326 / 100 * (2 / n) := by positivity
  refine ⟨22 * √(2 / (n : ℝ)) ^ 2, 35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ))), sd,
    1 / 10000, 51 / 10, 326 / 100 * (2 / n), by norm_num, by norm_num, by norm_num, hCS,
    hsd0, hsd', hL12, hS12, by positivity, by positivity, eps0_fixed_lt hn hsd, ?_, hbias⟩
  exact rootFL_fixed hn hsd hβ _ c (by norm_num) hCS hL12 hS12 _ _

/-- **Corollary at `n ≥ 23 000`** (floor `sd = 0.43`, `d_low = 0.1849`). -/
theorem classifier_paper_free23_root (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC)
    (hM : ∀ c ∈ goodC n (paperDesign n fT wT hf hw) EA,
      (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
      (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) ∧
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (43 / 100))
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_root_gen hn le_rfl (by unfold s0; norm_num)
    ((betaM_043 hn).trans (by norm_num)) fT wT hf hw t hEA hA hroom hM

/-- **Corollary at `n ≥ 80 000` with the paper's floor** (`sd = 0.4691`, `d_low = 0.22005`; the
paper's Part 08 uses `d_low = 0.22` and needs `(1 − η)d_low > 0.2`). -/
theorem classifier_paper_root80k (hn : 80000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC)
    (hM : ∀ c ∈ goodC n (paperDesign n fT wT hf hw) EA,
      (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
      (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) ∧
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (4691 / 10000))
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_root_gen (by omega) (by norm_num) (by unfold s0; norm_num)
    (betaM_4691 hn) fT wT hf hw t hEA hA hroom hM

end BstLean.Part165
