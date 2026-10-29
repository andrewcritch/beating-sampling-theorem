import BstLean.Part138Joint

/-!
# Part 138: the explicit second term at `ζ = 1/20`

Role: `delegations/statements/p138-spec.md`.

* `Omega2_le`: `Omega2 n (1/20) ≤ 2623/m`; `cRho_ge`: `cRho (1/20) ≥ 5.45`.
* **`EH_le`**: `EH n (1/20) ≤ 470·n/m` for `n ≥ 4096`, `m = mW n = ⌈n^{7/2}⌉`.
* **`cheapStandIn138_num`**: `E_W[1_good·(E_{μ_W} φ − E_{ν′_W} φ)²] ≤
    2·(0.99/n)·E_W[1_good·Var_{ν_W} φ] + 3760·B²·n/m`.
* `cheapStandIn138_total_num`, **`cheapStandIn138_tail_num`**: the total and the tail form.
* `cheapStandIn138_event_num`: for fixed `(M₁, M₂)` in `good138 n (1/20) p`:
  `E_{M₃}(E_{μ_W} φ − E_{ν′} φ)² ≤ 2·(0.99/n)·E_c Var_{ν_c} φ + 3760·B²·n/(m·p)`.
* `n_div_mW_sq`: `(n/m)² ≤ 1/n⁵` (so `n/m ≤ n^{−5/2}`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part138

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137

lemma rLow_ge : 6657 / 10000 ≤ rLow (1 / 20) := by
  unfold rLow zetaP wLow
  refine le_trans ?_ (le_max_right _ _)
  norm_num

lemma cRho_ge : 545 / 100 ≤ cRho (1 / 20) := by
  have hr := rLow_ge
  have hs : 81 / 100 ≤ √(rLow (1 / 20)) := by
    refine Real.le_sqrt_of_sq_le ?_
    refine le_trans ?_ hr
    norm_num
  unfold cRho
  have h1 : ((1 : ℝ) + 81 / 100) ^ 2 ≤ (1 + √(rLow (1 / 20))) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have h2 : (1 : ℝ) + 6657 / 10000 ≤ 1 + rLow (1 / 20) := by linarith
  have h3 := mul_le_mul h1 h2 (by norm_num) (by positivity)
  refine le_trans ?_ h3
  norm_num

section num

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

lemma Omega2_le : Omega2 n (1 / 20) ≤ 2623 / (mW n : ℝ) := by
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  set x : ℝ := 1 / (mW n : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx6 : x ≤ 1 / 1000000 := by
    rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hm6
  set q : ℝ := √x with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = x := Real.sq_sqrt hx0.le
  have e1 : 10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2 = 10 * x + 25 * x ^ 2 := by
    rw [hx]; ring
  have e2 : 2235 / 100 / (mW n : ℝ) = 2235 / 100 * x := by
    rw [hx]; ring
  have s1 : √(10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2) ≤ 317 / 100 * q := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 317 / 100 * q)]
    refine Real.sqrt_le_sqrt ?_
    rw [e1, mul_pow, hq2]
    nlinarith [mul_le_mul_of_nonneg_left hx6 hx0.le]
  have s2 : √(2235 / 100 / (mW n : ℝ)) ≤ 473 / 100 * q := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 473 / 100 * q)]
    refine Real.sqrt_le_sqrt ?_
    rw [e2, mul_pow, hq2]
    nlinarith
  unfold Omega2
  have h1 : 1 / (4936 / 10000 * (1 - (1 / 20 : ℝ)) ^ 2) *
      (√(10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2) +
        (2 + 1 / 20) * (√(2235 / 100 / (mW n : ℝ)) / (4936 / 10000))) ≤
      1 / (4936 / 10000 * (1 - (1 / 20 : ℝ)) ^ 2) *
      (317 / 100 * q + (2 + 1 / 20) * (473 / 100 * q / (4936 / 10000))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine add_le_add s1 (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    exact div_le_div_of_nonneg_right s2 (by norm_num)
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  refine h2.trans ?_
  have e3 : (1 / (4936 / 10000 * (1 - (1 / 20 : ℝ)) ^ 2) *
      (317 / 100 * q + (2 + 1 / 20) * (473 / 100 * q / (4936 / 10000)))) ^ 2 =
      (1 / (4936 / 10000 * (1 - (1 / 20 : ℝ)) ^ 2) *
        (317 / 100 + (2 + 1 / 20) * (473 / 100 / (4936 / 10000)))) ^ 2 * q ^ 2 := by ring
  rw [e3, hq2, div_eq_mul_one_div (2623 : ℝ), ← hx]
  refine mul_le_mul_of_nonneg_right ?_ hx0.le
  norm_num

lemma Beta_le : Beta n (1 / 20) ≤ 40700 / (mW n : ℝ) := by
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  set x : ℝ := 1 / (mW n : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx6 : x ≤ 1 / 1000000 := by
    rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hm6
  have e : Beta n (1 / 20) =
      (10 * x + 25 * x ^ 2 + 2235 / 100 * x / (4936 / 10000) ^ 2) / (1 / 20) ^ 2 := by
    unfold Beta; rw [hx]; ring
  rw [e, div_eq_mul_one_div (40700 : ℝ), ← hx]
  have := mul_le_mul_of_nonneg_left hx6 hx0.le
  norm_num
  nlinarith

/-- **The explicit size of `EH`**: `EH n (1/20) ≤ 470·n/m` for `n ≥ 4096`. -/
theorem EH_le : EH n (1 / 20) ≤ 470 * (n : ℝ) / (mW n : ℝ) := by
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set x : ℝ := 1 / (mW n : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have h1 := Omega2_le hn
  have h2 := Beta_le hn
  rw [div_eq_mul_one_div (2623 : ℝ), ← hx] at h1
  rw [div_eq_mul_one_div (40700 : ℝ), ← hx] at h2
  have hc := cRho_ge
  have hw := wLow_pos
  have hk : (n : ℝ) / (wLow ^ 2 * cRho (1 / 20)) ≤ (n : ℝ) * (1749 / 10000) := by
    have a1 : (n : ℝ) / (wLow ^ 2 * cRho (1 / 20)) ≤ (n : ℝ) / (wLow ^ 2 * (545 / 100)) :=
      div_le_div_of_nonneg_left hn0.le (by positivity)
        (mul_le_mul_of_nonneg_left hc (by positivity))
    refine a1.trans ?_
    rw [div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ hn0.le
    unfold wLow
    norm_num
  have hO0 := Omega2_nonneg n (1 / 20)
  have h3 : (n : ℝ) / (wLow ^ 2 * cRho (1 / 20)) * Omega2 n (1 / 20) ≤
      (n : ℝ) * (1749 / 10000) * (2623 * x) :=
    mul_le_mul hk h1 hO0 (by positivity)
  unfold EH
  rw [div_eq_mul_one_div (470 * (n : ℝ)), ← hx]
  have h4 : 40700 * x ≤ 10 * (n : ℝ) * x := by
    refine mul_le_mul_of_nonneg_right ?_ hx0.le
    linarith
  have h5 : 0 ≤ (n : ℝ) * x := by positivity
  nlinarith

/-- `(n/m)² ≤ 1/n⁵`: the second term is of order `B²·n^{−5/2}`. -/
lemma n_div_mW_sq : ((n : ℝ) / (mW n : ℝ)) ^ 2 ≤ 1 / (n : ℝ) ^ 5 := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  have h := mW_sq_ge n
  have h' : (n : ℝ) ^ 7 ≤ (mW n : ℝ) ^ 2 := by exact_mod_cast h
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (n : ℝ) ^ 2 * (n : ℝ) ^ 5 = (n : ℝ) ^ 7 := by ring
    _ ≤ (mW n : ℝ) ^ 2 := h'
    _ = 1 * (mW n : ℝ) ^ 2 := by ring

variable {φ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, |φ x| ≤ B)

include hφ hB

/-- **The cheap stand-in theorem, joint form with the explicit second term (item 3).** For
`n ≥ 4096`, `m = mW n` and measurable `φ` with `|φ| ≤ B`:
`E_W[1_good·(E_{μ_W} φ − E_{ν′_W} φ)²] ≤
   2·(0.99/n)·E_W[1_good·Var_{ν_W} φ] + 3760·B²·n/m`. -/
theorem cheapStandIn138_num :
    ∫ W, (goodW n).indicator
        (fun W => ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W) ^ 2) W
        ∂mlpGauss (2 * n) (mW n) n ≤
      2 * (99 / 100 / (n : ℝ) *
        ∫ W, (goodW n).indicator (fun W => Var[φ; nuW W]) W ∂mlpGauss (2 * n) (mW n) n) +
      3760 * B ^ 2 * ((n : ℝ) / (mW n : ℝ)) := by
  have h := cheapStandIn138_joint hn (by norm_num : (0 : ℝ) < 1 / 20) (by norm_num) hφ hB
  have h2 := mul_le_mul_of_nonneg_left (EH_le hn) (by positivity : (0 : ℝ) ≤ 8 * B ^ 2)
  have e : 8 * B ^ 2 * (470 * (n : ℝ) / (mW n : ℝ)) = 3760 * B ^ 2 * ((n : ℝ) / (mW n : ℝ)) := by
    ring
  linarith

/-- The total form with the explicit second term:
`E_W(E_{μ_W} φ − E_{ν′_W} φ)² ≤ 2·(0.99/n)·E_W Var_{ν_W} φ + 3760·B²·n/m + 0.008·B²`. -/
theorem cheapStandIn138_total_num :
    ∫ W, ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W) ^ 2 ∂mlpGauss (2 * n) (mW n) n ≤
      2 * (99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂mlpGauss (2 * n) (mW n) n) +
        3760 * B ^ 2 * ((n : ℝ) / (mW n : ℝ)) + 8 / 1000 * B ^ 2 := by
  have h := cheapStandIn138_total hn (by norm_num : (0 : ℝ) < 1 / 20) (by norm_num) hφ hB
  have h2 := mul_le_mul_of_nonneg_left (EH_le hn) (by positivity : (0 : ℝ) ≤ 8 * B ^ 2)
  have e : 8 * B ^ 2 * (470 * (n : ℝ) / (mW n : ℝ)) = 3760 * B ^ 2 * ((n : ℝ) / (mW n : ℝ)) := by
    ring
  linarith

/-- **The tail form with the explicit second term (item 4).** For `t > 0`:
`Pr_W(|E_{μ_W} φ − E_{ν′_W} φ| ≥ t) ≤
   0.002 + (2·(0.99/n)·E_W Var_{ν_W} φ + 3760·B²·n/m)/t²`. -/
theorem cheapStandIn138_tail_num {t : ℝ} (ht : 0 < t) :
    (mlpGauss (2 * n) (mW n) n).real
        {W | t ≤ |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W|} ≤
      2 / 1000 +
        (2 * (99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂mlpGauss (2 * n) (mW n) n) +
          3760 * B ^ 2 * ((n : ℝ) / (mW n : ℝ))) / t ^ 2 := by
  have h := cheapStandIn138_tail hn (by norm_num : (0 : ℝ) < 1 / 20) (by norm_num) hφ hB ht
  have h2 := mul_le_mul_of_nonneg_left (EH_le hn) (by positivity : (0 : ℝ) ≤ 8 * B ^ 2)
  have e : 8 * B ^ 2 * (470 * (n : ℝ) / (mW n : ℝ)) = 3760 * B ^ 2 * ((n : ℝ) / (mW n : ℝ)) := by
    ring
  refine h.trans (add_le_add le_rfl (div_le_div_of_nonneg_right ?_ (by positivity)))
  linarith

/-- **For fixed `(M₁, M₂)` in the event `good138 n (1/20) p`** (probability at least
`0.998 − p`), with the expectation over `M₃`:
`E(E_{μ_W} φ − E_{ν′} φ)² ≤ 2·(0.99/n)·E_c Var_{ν_c} φ + 3760·B²·n/(m·p)`. -/
theorem cheapStandIn138_event_num {p : ℝ} (hp : 0 < p) {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ good138 n (1 / 20) p) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂cheapIn (M₃.mulVec (hbarW θ)) (tau0 (2 * n) (mW n) θ)) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
      2 * (99 / 100 / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (hbarW θ) c] ∂cDist n (2 / (mW n : ℝ)) (hbarW θ)) +
      3760 * B ^ 2 * ((n : ℝ) / (mW n : ℝ)) / p := by
  have h := cheapStandIn138_event hn (by norm_num : (0 : ℝ) ≤ 1 / 20) (by norm_num) hθ hφ hB
  have h1 : EH n (1 / 20) / p ≤ 470 * (n : ℝ) / (mW n : ℝ) / p :=
    div_le_div_of_nonneg_right (EH_le hn) hp.le
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 8 * B ^ 2)
  have e : 8 * B ^ 2 * (470 * (n : ℝ) / (mW n : ℝ) / p) =
      3760 * B ^ 2 * ((n : ℝ) / (mW n : ℝ)) / p := by ring
  linarith

end num

end BstLean.Part138

open BstLean.Part138 in
#print axioms EH_le
open BstLean.Part138 in
#print axioms cheapStandIn138_num
open BstLean.Part138 in
#print axioms cheapStandIn138_tail_num
open BstLean.Part138 in
#print axioms cheapStandIn138_event_num
