import BstLean.Part150DispS
import BstLean.Part150Arith
import BstLean.Part150Prog5

/-!
# Part 150, item 5: a Lean success bound for the ARITHMETIC program

Role: `delegations/statements/p150-spec.md`, item 5.

The program `fullProg150 k n J` (`Part150Prog5`) is ONE straight-line program in `RProg`
(operations `+ − × ÷ √ relu`, rational constants; no oracle): the `W` stage of Part 141/149,
the arithmetic pass over `A` with binomial sums (`J + 1` atoms in both layers), then `k` forward
passes of `F`. It applies `A` to no input.

* `pFail6_149`, **`displaceSamp150`**: the frame of `Part150DispS` with the parameters of
  `onePassA149`.
* **`arithMean150`**: the exact mean over the last Gaussian vector (centre `bTW J`).
* **`arithSamp150`**: the sample mean with `k` forward passes of `F`.
* **`arithProg150`**: the output of the program `fullProg150 k n J`:
  `Pr(|output − B| ≤ sd/2) ≥ 1 − pArith`, the probability over `(W, A, F)` and the `k` Gaussian
  vectors.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part141 BstLean.Part145
open BstLean.Part149

variable {n : ℕ}

/-- The formula `pFail6` at the parameters of `onePassA149`, `D4 = 1/25`, `y4 = 0.9193`. -/
theorem pFail6_149 (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {ξ η₄ η₅ : ℝ} (hξ0 : 0 ≤ ξ)
    (hη₄ : 0 < η₄) (hη₅ : 0 < η₅) :
    pFail6 n k (284 / 10000) (635 / 10000) (12522 / 10000) (1908 / 1000) (273 / 1000) (251 / 1000) (51 / 10) (56 / 1000) (1 / 10) 24 (95 / 100) (393278 / 1000000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2) (16034 / 100000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2) (4728 / 1000 * (1 / √(n : ℝ)) ^ 2) (9 / 100) (1 / 10) (88 / 100) (67 / 1000) (8441 / 10000) (9 / 100) (31 / 100) (534859 / 1000000 * (1 / √(n : ℝ)) + 12510 / 1000 * (1 / √(n : ℝ)) ^ 2) η₄ ξ (1 / 25) (9193 / 10000) η₅ ≤
      (1 + η₅) * ((1 + η₄) * p149 n + ξ * (625 + (1 + 1 / η₄) * 235)) +
        (1 + 1 / η₅) * (19 / k) := by
  have h5 := pFail5_149 hn hξ0 hη₄
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hxi : 0 ≤ xiB n (9 / 100) (88 / 100) (9 / 100)
      (534859 / 1000000 * (1 / √(n : ℝ)) + 12510 / 1000 * (1 / √(n : ℝ)) ^ 2) := by
    unfold xiB cQ3 cD3 Kq; positivity
  have hX := X_le_pFail3 (n := n) (Δmax := 284 / 10000) (ΔXmax := 635 / 10000)
    (r₁ := 12522 / 10000) (r₂ := 1908 / 1000) (w := 273 / 1000) (g := 251 / 1000) (η := 51 / 10)
    (ζ := 56 / 1000) (ζ₂ := 1 / 10) (η₁ := 24) (θ := 95 / 100)
    (ΔKb := 393278 / 1000000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2)
    (ΔXb := 16034 / 100000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2)
    (δb := 4728 / 1000 * (1 / √(n : ℝ)) ^ 2) (εQ := 1 / 10) (Dmax := 67 / 1000)
    (yhi := 8441 / 10000) (η₃ := 31 / 100) hxi (by norm_num) (by norm_num)
  unfold pFail6
  unfold pFail5 at h5 ⊢
  set P3 := pFail3 n (284 / 10000) (635 / 10000) (12522 / 10000) (1908 / 1000) (273 / 1000) (251 / 1000) (51 / 10) (56 / 1000) (1 / 10) 24 (95 / 100) (393278 / 1000000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2) (16034 / 100000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2) (4728 / 1000 * (1 / √(n : ℝ)) ^ 2) (9 / 100) (1 / 10) (88 / 100) (67 / 1000) (8441 / 10000) (9 / 100) (31 / 100) (534859 / 1000000 * (1 / √(n : ℝ)) + 12510 / 1000 * (1 / √(n : ℝ)) ^ 2) with hP3
  set a3 := aE3 n (284 / 10000) (635 / 10000) (12522 / 10000) (1908 / 1000) (273 / 1000)
    (251 / 1000) (51 / 10) (56 / 1000) (1 / 10) 24
    (393278 / 1000000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2)
    (16034 / 100000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2)
    (4728 / 1000 * (1 / √(n : ℝ)) ^ 2) (9 / 100) (88 / 100) (8441 / 10000) (9 / 100) (31 / 100)
    (534859 / 1000000 * (1 / √(n : ℝ)) + 12510 / 1000 * (1 / √(n : ℝ)) ^ 2) with ha3
  set D : ℝ := 95 / 100 * (4 / (n : ℝ) * (222757 / 1000000)) with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  set aH : ℝ := 2 / (n : ℝ) * (2 / (1 - 9193 / 10000)) * ξ with haH
  have haH0 : 0 ≤ aH := by rw [haH]; positivity
  have e1 : 4 * ((1 + η₄) * a3 + (1 + 1 / η₄) * aH) / D =
      4 * a3 / D + η₄ * (4 * a3 / D) + (1 + 1 / η₄) * (4 * aH / D) := by ring
  have hξD : 0 ≤ ξ / (1 / 25 : ℝ) ^ 2 := by positivity
  have hX' : 4 * ((1 + η₄) * a3 + (1 + 1 / η₄) * aH) / D ≤
      P3 + η₄ * (4 * a3 / D) + ξ / (1 / 25 : ℝ) ^ 2 + (1 + 1 / η₄) * (4 * aH / D) := by
    rw [e1]; linarith
  have h7 := mul_le_mul_of_nonneg_left hX' hη₅.le
  have eZ : 4 * (4 / (n : ℝ) / k) / D = 4 / (k : ℝ) / (95 / 100 * (222757 / 1000000)) := by
    rw [hD]
    have hn0 : (n : ℝ) ≠ 0 := hx0.ne'
    field_simp
  have nZ : 4 / (k : ℝ) / (95 / 100 * (222757 / 1000000)) ≤ 19 / k := by
    rw [div_div, div_le_div_iff₀ (by positivity) hk0]
    nlinarith
  have hη' : (0 : ℝ) ≤ 1 + 1 / η₅ := by positivity
  have h8 := mul_le_mul_of_nonneg_left (eZ.le.trans nZ) hη'
  have h9 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 1 + η₅)
  nlinarith

/-- **A program with another centre and `k` forward passes of `F` succeeds**, with the
parameters of `onePassA149`. -/
theorem displaceSamp150 (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {bh : CMap n} (hbh : Measurable bh)
    {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ : DispOK n (Gwin n) (9 / 100) (1 / 10) bh ξ) {η₄ η₅ : ℝ}
    (hη₄ : 0 < η₄) (hη₅ : 0 < η₅) :
    1 - ((1 + η₅) * ((1 + η₄) * p149 n + ξ * (625 + (1 + 1 / η₄) * 235)) +
        (1 + 1 / η₅) * (19 / k)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real
        {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
          sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have h6 := pFail6_149 hn hk hξ0 hη₄ hη₅
  have hn1 : 1 ≤ n := by omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hst : √(n : ℝ) = 1 / t := by rw [ht]; field_simp
  have hnt : (n : ℝ) = 1 / t ^ 2 := by
    rw [ht, div_pow, one_pow, Real.sq_sqrt hx0.le]; field_simp
  have ht2 : t ^ 2 = 1 / (n : ℝ) := by rw [hnt]; field_simp
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmA6 : 1000000 ≤ mA n := by
    unfold mA
    calc 1000000 ≤ 4096 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  have hcF : cF2o (mA n) ≤ 4728 / 1000 * t ^ 2 := by
    have h1 := BstLean.Part136.cF2o_sq_le hmA6
    have h0 := (BstLean.Part136.cF2o_pos hmA).le
    rw [mA_eqR] at h1
    have h2 : (2235 : ℝ) / 100 / (n : ℝ) ^ 2 = 2235 / 100 * (t ^ 2) ^ 2 := by
      rw [ht2]; field_simp
    rw [h2] at h1
    have h3 : cF2o (mA n) ^ 2 ≤ (4728 / 1000 * t ^ 2) ^ 2 := by
      refine h1.trans ?_
      have : 0 ≤ (t ^ 2) ^ 2 := by positivity
      nlinarith
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq h3 (by positivity))
  have hΔK : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dK2 n (mA n) q ≤ 393278 / 1000000 * t + 11363 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dK2_le hn hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hΔX : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dX2 n (mA n) q ≤ 16034 / 100000 * t + 11363 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dX2_le hn hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dQ1 n (mA n) q ≤ 534859 / 1000000 * t + 12510 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dQ1_le hn hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hP : POK2 (6662 / 10000) (6969 / 10000) (284 / 10000) (635 / 10000) (12522 / 10000)
      (1908 / 1000) (273 / 1000) (251 / 1000) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hP3 : POK3 (6969 / 10000) (284 / 10000) (9 / 100) (1 / 10) (88 / 100) (67 / 1000)
      (8517 / 10000) (8441 / 10000) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hsq : √(8441 / 10000 : ℝ) ≤ 91876 / 100000 := by
    rw [Real.sqrt_le_iff]; norm_num
  have hy4 : (√(8441 / 10000 : ℝ) + 1 / 25) ^ 2 ≤ 9193 / 10000 := by
    have h0 := Real.sqrt_nonneg (8441 / 10000 : ℝ)
    nlinarith
  have h := displaceSamp150_formula hn hk hP (η₄ := η₄) hη₄ (η₅ := η₅) hη₅ hP3 (ζ₃ := 9 / 100)
    (by norm_num) (η₃ := 31 / 100)
    (by norm_num) (dQb := 534859 / 1000000 * t + 12510 / 1000 * t ^ 2) hdQ
    (fun q hq1 hq2 => dQ1_nonneg hq1 hq2 hn1)
    (η := 51 / 10) (by norm_num) (ζ := 56 / 1000)
    (by norm_num) (ζ₂ := 1 / 10) (by norm_num) (η₁ := 24) (by norm_num) (θ := 95 / 100)
    (by norm_num) (by norm_num) (ΔKb := 393278 / 1000000 * t + 11363 / 1000 * t ^ 2)
    (ΔXb := 16034 / 100000 * t + 11363 / 1000 * t ^ 2) (by positivity) (by positivity) hΔK
    (fun q hq1 hq2 => dK2_nonneg hq1 hq2 hn1) hΔX (fun q _ _ => dX2_nonneg hn1) hcF
    hbh (D4 := 1 / 25) (y4 := 9193 / 10000) (by norm_num) hy4 (by norm_num) hξ0 hξ
  refine le_trans ?_ h
  exact sub_le_sub_left h6 1

/-! ## The arithmetic centre -/

/-- The bound of the first-layer kernel error of Part 149 (`dQ1_le`). -/
noncomputable def dQb149 (n : ℕ) : ℝ := 534859 / 1000000 / √(n : ℝ) + 12510 / 1000 / (n : ℝ)

/-- The displacement constant of the arithmetic centre with `J + 1` atoms, at the thresholds
`εD = 9/100`, `εQ = 1/10` of `onePassA149`; `lam > 0` is a free parameter. -/
noncomputable def xiA (n J : ℕ) (lam : ℝ) : ℝ := xiArith n J (9 / 100) (1 / 10) lam (dQb149 n)

lemma xiA_nonneg (n J : ℕ) {lam : ℝ} (hlam : 0 < lam) : 0 ≤ xiA n J lam := by
  have h1 := xiBin_nonneg J
  have h2 := CQn_nonneg (n := n) (εD := 9 / 100) (εQ := 1 / 10) (by norm_num) (by norm_num)
    (by norm_num) hlam
  have h3 := CEn_nonneg (n := n) (εD := 9 / 100) (εQ := 1 / 10) (by norm_num) (by norm_num)
    (by norm_num)
  have h4 := C0n_nonneg (n := n) (εD := 9 / 100) (εQ := 1 / 10) (by norm_num) (by norm_num)
    (by norm_num) hlam
  unfold xiA xiArith
  positivity

/-- The arithmetic centre is close to the oracle centre of Part 149, in mean on the good event. -/
theorem arith_dispOK_149 (hn : 4096 ≤ n) {J : ℕ} (hJ : 1 ≤ J) {lam : ℝ} (hlam : 0 < lam) :
    DispOK n (Gwin n) (9 / 100) (1 / 10) (bTW J) (xiA n J lam) :=
  arith_dispOK hn (goodEvFR hn).to0 (winOK2_149 hn) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hlam hJ (fun _ h1 h2 => dQ1_le hn h1 h2)
    (fun _ h1 h2 => dQ1_nonneg h1 h2 (by omega))

/-- **The arithmetic centre, exact mean over the last Gaussian vector.** -/
theorem arithMean150 (hn : 4096 ≤ n) {J : ℕ} (hJ : 1 ≤ J) {lam η₄ : ℝ} (hlam : 0 < lam)
    (hη₄ : 0 < η₄) :
    1 - ((1 + η₄) * p149 n + xiA n J lam * (625 + (1 + 1 / η₄) * 235)) ≤
      (mlpTriple 2 n).real
        {t | |gOutH (bTW J) t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2| ≤
          sdn t.1 t.2.1 t.2.2 / 2} :=
  displace150 hn (measurable_bTW J) (xiA_nonneg n J hlam) (arith_dispOK_149 hn hJ hlam) hη₄

/-- **The arithmetic centre with `k` forward passes of `F`.** -/
theorem arithSamp150 (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {J : ℕ} (hJ : 1 ≤ J) {lam η₄ η₅ : ℝ}
    (hlam : 0 < lam) (hη₄ : 0 < η₄) (hη₅ : 0 < η₅) :
    1 - ((1 + η₅) * ((1 + η₄) * p149 n + xiA n J lam * (625 + (1 + 1 / η₄) * 235)) +
        (1 + 1 / η₅) * (19 / k)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real
        {p | |gSampH (bTW J) k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
          sdn p.1.1 p.1.2.1 p.1.2.2 / 2} :=
  displaceSamp150 hn hk (measurable_bTW J) (xiA_nonneg n J hlam) (arith_dispOK_149 hn hJ hlam)
    hη₄ hη₅

/-! ## The program -/

lemma mulVec_bTW (J : ℕ) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n) :
    A.2.2.mulVec (bTW J (W, thA A)) = cT J J A.1 A.2.1 A.2.2 (cenA W) (tauWA W) := by
  funext i
  unfold bTW cT
  rw [Matrix.mulVec_smul]
  simp only [thA, Pi.smul_apply, smul_eq_mul]
  ring

lemma tauOutOf_bTW (J : ℕ) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n) :
    tauOutOf n (bTW J (W, thA A)) = sigT J J A.1 A.2.1 (cenA W) (tauWA W) := by
  unfold tauOutOf sigT bTW
  rw [normSq_smul]
  simp only [thA]
  congr 2
  ring

/-- The output of the program is the sample mean of the arithmetic centre, when `τ̃₀ > 0`. -/
theorem fullProg150_gSampH {k J : ℕ} (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (F : MlpParam n (mF n) 1) (γ : Fin k → Fin n → ℝ) (hτ : 0 < tauWA W) :
    (fullProg150 k n J).eval (fullVal W A F γ) () = gSampH (bTW J) k W A F γ := by
  rw [fullProg150_eval W A F γ hτ]
  unfold gSampH preH
  rw [mulVec_bTW, tauOutOf_bTW]

/-- **The arithmetic program succeeds.** `fullProg150 k n J` is one straight-line program (no
oracle; it applies `A` to no input). For every `n ≥ 4096`, `k ≥ 1`, `J ≥ 1` and every
`lam, η₄, η₅ > 0`:
`Pr_{W, A, F, γ}(|output − B| ≤ sd/2) ≥
  1 − ((1 + η₅)((1 + η₄)·p149 n + xiA n J lam·(625 + (1 + 1/η₄)·235)) + (1 + 1/η₅)·19/k + 1/n)`. -/
theorem arithProg150 (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {J : ℕ} (hJ : 1 ≤ J) {lam η₄ η₅ : ℝ}
    (hlam : 0 < lam) (hη₄ : 0 < η₄) (hη₅ : 0 < η₅) :
    1 - ((1 + η₅) * ((1 + η₄) * p149 n + xiA n J lam * (625 + (1 + 1 / η₄) * 235)) +
        (1 + 1 / η₅) * (19 / k) + 1 / (n : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real
        {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
            Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hS := arithSamp150 hn hk hJ hlam hη₄ hη₅
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hG := (goodEvFR hn).to0
  have hwin := winOK2_149 hn
  have hG1 : (hidGauss (2 * n) (mW n)).real (Gwin n)ᶜ ≤ 1 / 50000 / (n : ℝ) := by
    have h := Gwin_compl_n hn
    unfold cW at h
    have e : (15640 : ℝ) / 1073741824 / (n : ℝ) ≤ 1 / 50000 / (n : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hx0.le
    linarith
  have hbadW := badAG0_prob_gen hn hG hG1
  set μ' := (mlpTriple 2 n).prod (gamK k n) with hμ'
  set ES : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | |gSampH (bTW J) k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
      sdn p.1.1 p.1.2.1 p.1.2.2 / 2} with hES
  set EP : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
      Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} with hEP
  have hsub : ES ⊆ EP ∪ {p | p.1 ∈ {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 | t.1 ∉ goodWAG (Gwin n)}} := by
    intro p hp
    by_cases hW : p.1.1 ∈ goodWAG (Gwin n)
    · refine Or.inl ?_
      have hτ : 0 < tauWA p.1.1 := (hwin (p.1.1.1, p.1.1.2.1) hW).2.1
      show |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2
      rw [fullProg150_gSampH p.1.1 p.1.2.1 p.1.2.2 p.2 hτ]
      exact hp
    · exact Or.inr hW
  have hm := measureReal_mono (μ := μ') hsub (measure_ne_top _ _)
  have hu := measureReal_union_le (μ := μ') EP
    {p | p.1 ∈ {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 | t.1 ∉ goodWAG (Gwin n)}}
  have hpf := BstLean.Part139.prod_fst_real (mlpTriple 2 n) (gamK k n)
    {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      t.1 ∉ goodWAG (Gwin n)}
  rw [← hμ'] at hpf
  have hq : (1 : ℝ) / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 ≤ 1 / (n : ℝ) := by
    rw [qA_cast]
    have e1 : (68000000 : ℝ) / (10000 * (n : ℝ)) ^ 2 = 68 / 100 / (n : ℝ) ^ 2 := by
      field_simp; ring
    have e2 : (68 : ℝ) / 100 / (n : ℝ) ^ 2 ≤ 1 / 2 / (n : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hx0]
      nlinarith
    have e3 : (1 : ℝ) / 50000 / (n : ℝ) ≤ 1 / 2 / (n : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hx0.le
    rw [e1]
    have e4 : (1 : ℝ) / 2 / (n : ℝ) + 1 / 2 / (n : ℝ) = 1 / (n : ℝ) := by ring
    linarith
  linarith

end BstLean.Part150

open BstLean.Part150 in
#print axioms displaceSamp150
open BstLean.Part150 in
#print axioms arithMean150
open BstLean.Part150 in
#print axioms arithSamp150
open BstLean.Part150 in
#print axioms arithProg150
