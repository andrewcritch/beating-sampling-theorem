import BstLean.Part169Grid
import BstLean.Part169Red

/-!
# Part 169 (file `Lip`): the grid error of the passes (paper `t7:p08:grid`)

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, "Use also `E_{2op}`": on the operator events
`|∇_x f| ≤ Λ/√n`, `|a₂(x)| ≤ Λ`, `|∇_x ω| ≤ 2Λ²/n`, `Λ = O₁O₂`; the meridian derivative has
length `(1 − s²)^{−1/2}`; so the latitude means have the Lipschitz constants
`L_f = Λ/√(nq)`, `L_ω = 2Λ²/(n√q)` (`q ≤ 1 − s²` on the bulk), and
`n|Δ_f^grid| ≤ nL_fΔ/2`, `n|Δ_ω^grid| ≤ nL_ωΔ/2` (formula `t7:p08:grid`).

The operator events enter as hypotheses `OpB A O : ∀ z, |Az|² ≤ O²|z|²`.

* `hid2_sub_le`, `hid2_le`: `|a₂(x) − a₂(y)|² ≤ Λ²|x − y|²`, `|a₂(x)|² ≤ Λ²|x|²`.
* `xLat_sub_le`: `|x_s(v) − x_{s'}(v)|² ≤ (s − s')²/q` when `s², s'² ≤ 1 − q`.
* `fX`, `wX`: `f(x) = ⟨a₂(x), b⟩/(√n|b|)`, `ω(x) = |a₂(x)|²/n`; `fbarS`, `wbarS`: their full
  latitude means at the latitude `s`.
* **`fbar_lip`**, **`wbar_lip`**: `|f̄(s) − f̄(s')| ≤ Λ|s − s'|/√(nq)`,
  `|ω̄(s) − ω̄(s')| ≤ 2Λ²|s − s'|/(n√q)`.
* `fbR_eq`, `wbR_eq`: Part 169's `fbR`, `wbR` are `fbarS`, `wbarS` at the latitude of the index.
* **`grid_f`**, **`grid_w`**: on a kept index (latitude in `[L, H]`) and with `s² ≤ 1 − q` on
  `[L, H]`: `|f̄(s) − f̄(s_g)| ≤ ΛΔ/(2√(nq))`, `|ω̄(s) − ω̄(s_g)| ≤ Λ²Δ/(n√q)`.
-/

namespace BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (xLat hhMat uHat consV latC Ix lamX bulkI bulkIx keptIx hh_normSq
  normSq_consV)
open BstLean.Part162 (lbar)
open BstLean.Part53 (unitF53 measurable_unitF)

variable {n : ℕ}

/-- The operator bound `|Az|² ≤ O²|z|²` for every `z`. -/
def OpB {k m : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (O : ℝ) : Prop :=
  ∀ z, normSq (A.mulVec z) ≤ O ^ 2 * normSq z

lemma normSq_reluV_sub {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    normSq (reluV a - reluV b) ≤ normSq (a - b) := by
  unfold normSq
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.sub_apply, reluV]
  have := BstLean.Part142.abs_relu_sub_le (a i) (b i)
  exact sq_le_sq.mpr this

lemma normSq_reluV_le' {ι : Type*} [Fintype ι] (a : ι → ℝ) : normSq (reluV a) ≤ normSq a := by
  have h := normSq_reluV_sub a 0
  have e : reluV (0 : ι → ℝ) = 0 := by funext i; simp [reluV, relu]
  rwa [e, sub_zero, sub_zero] at h

/-- `|a₂(x) − a₂(y)|² ≤ O₂²O₁²|x − y|²`. -/
lemma hid2_sub_le {k m₁ m₂ : ℕ} {A₁ : Matrix (Fin m₁) (Fin k) ℝ} {A₂ : Matrix (Fin m₂) (Fin m₁) ℝ}
    {O₁ O₂ : ℝ} (h1 : OpB A₁ O₁) (h2 : OpB A₂ O₂) (x y : Fin k → ℝ) :
    normSq (hid2 A₁ A₂ x - hid2 A₁ A₂ y) ≤ O₂ ^ 2 * (O₁ ^ 2 * normSq (x - y)) := by
  unfold hid2
  refine (normSq_reluV_sub _ _).trans ?_
  rw [← Matrix.mulVec_sub]
  refine (h2 _).trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  refine (normSq_reluV_sub _ _).trans ?_
  rw [← Matrix.mulVec_sub]
  exact h1 _

/-- `|a₂(x)|² ≤ O₂²O₁²|x|²`. -/
lemma hid2_le {k m₁ m₂ : ℕ} {A₁ : Matrix (Fin m₁) (Fin k) ℝ} {A₂ : Matrix (Fin m₂) (Fin m₁) ℝ}
    {O₁ O₂ : ℝ} (h1 : OpB A₁ O₁) (h2 : OpB A₂ O₂) (x : Fin k → ℝ) :
    normSq (hid2 A₁ A₂ x) ≤ O₂ ^ 2 * (O₁ ^ 2 * normSq x) := by
  have h := hid2_sub_le h1 h2 x 0
  have e : hid2 A₁ A₂ 0 = 0 := by
    unfold hid2; rw [Matrix.mulVec_zero]
    have : reluV (0 : Fin m₁ → ℝ) = 0 := by funext i; simp [reluV, relu]
    rw [this, Matrix.mulVec_zero]; funext i; simp [reluV, relu]
  rwa [e, sub_zero, sub_zero] at h

lemma consV_sub (z z' : ℝ) (g g' : Fin (n - 1) → ℝ) :
    consV (n := n) z g - consV z' g' = consV (z - z') (g - g') := by
  funext i
  unfold consV
  by_cases h : (i : ℕ) = 0 <;> simp [h]

/-- **The meridian bound**: `|x_s(v) − x_{s'}(v)|² ≤ (s − s')²/q` for `s², s'² ≤ 1 − q`. -/
lemma xLat_sub_le (hn : 1 ≤ n) (c : Ret n) {s s' q : ℝ} (hq : 0 < q) (hs : s ^ 2 ≤ 1 - q)
    (hs' : s' ^ 2 ≤ 1 - q) (v : Fin (n - 1) → ℝ) :
    normSq (xLat c s (unitF53 v) - xLat c s' (unitF53 v)) ≤ (s - s') ^ 2 / q := by
  unfold xLat
  rw [← Matrix.mulVec_sub, hh_normSq, consV_sub, normSq_consV hn, ← sub_smul]
  have hu : normSq (unitF53 v) ≤ 1 := by
    have h := BstLean.Part162.radF_unitF_le v
    have h3 : normSq (unitF53 v) = BstLean.Part53.radF53 (unitF53 v) ^ 2 :=
      (BstLean.Part162.radF_sq _).symm
    rw [h3]
    have := BstLean.Part162.radF_nonneg (unitF53 v)
    nlinarith
  have hsm : normSq ((√(1 - s ^ 2) - √(1 - s' ^ 2)) • unitF53 v) =
      (√(1 - s ^ 2) - √(1 - s' ^ 2)) ^ 2 * normSq (unitF53 v) := by
    unfold normSq; simp only [Pi.smul_apply, smul_eq_mul, mul_pow]; rw [Finset.mul_sum]
  rw [hsm]
  set A := √(1 - s ^ 2)
  set B := √(1 - s' ^ 2)
  have hA : √q ≤ A := Real.sqrt_le_sqrt (by linarith)
  have hB : √q ≤ B := Real.sqrt_le_sqrt (by linarith)
  have hsq0 : 0 < √q := Real.sqrt_pos.mpr hq
  have hA2 : A ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (by nlinarith)
  have hB2 : B ^ 2 = 1 - s' ^ 2 := Real.sq_sqrt (by nlinarith)
  -- `(A − B)² (A + B)² = (s'² − s²)² = (s − s')²(s + s')²` and `(s + s')² ≤ 4(1 − q)`
  have hss : (s + s') ^ 2 ≤ 4 * (1 - q) := by nlinarith [sq_nonneg (s - s')]
  have hAB : 2 * √q ≤ A + B := by linarith
  have hAB2 : 4 * q ≤ (A + B) ^ 2 := by
    have := Real.sq_sqrt hq.le
    nlinarith
  have key : (A - B) ^ 2 * (A + B) ^ 2 = (s - s') ^ 2 * (s + s') ^ 2 := by
    have : (A - B) * (A + B) = (s' - s) * (s' + s) := by nlinarith
    calc (A - B) ^ 2 * (A + B) ^ 2 = ((A - B) * (A + B)) ^ 2 := by ring
      _ = ((s' - s) * (s' + s)) ^ 2 := by rw [this]
      _ = (s - s') ^ 2 * (s + s') ^ 2 := by ring
  have hAmB : (A - B) ^ 2 ≤ (s - s') ^ 2 * (1 - q) / q := by
    rw [le_div_iff₀ hq]
    have h4 : (A - B) ^ 2 * (4 * q) ≤ (s - s') ^ 2 * (4 * (1 - q)) := by
      calc (A - B) ^ 2 * (4 * q) ≤ (A - B) ^ 2 * (A + B) ^ 2 :=
            mul_le_mul_of_nonneg_left hAB2 (sq_nonneg _)
        _ = (s - s') ^ 2 * (s + s') ^ 2 := key
        _ ≤ (s - s') ^ 2 * (4 * (1 - q)) := mul_le_mul_of_nonneg_left hss (sq_nonneg _)
    nlinarith
  have h2 : (A - B) ^ 2 * normSq (unitF53 v) ≤ (A - B) ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg _) hu
  have e : (s - s') ^ 2 / q = (s - s') ^ 2 + (s - s') ^ 2 * (1 - q) / q := by
    field_simp; ring
  rw [e]; linarith

/-! ## The fields `f`, `ω` and their latitude means -/

/-- `f(x) = ⟨a₂(x), b⟩/(√n|b|)`. -/
noncomputable def fX (c : Ret n) (x : Fin n → ℝ) : ℝ :=
  (∑ j, hid2 (A1 c) (A2 c) x j * bR c j) / (√(n : ℝ) * √(normSq (bR c)))

/-- `ω(x) = |a₂(x)|²/n`. -/
noncomputable def wX (c : Ret n) (x : Fin n → ℝ) : ℝ := normSq (hid2 (A1 c) (A2 c) x) / (n : ℝ)

/-- `f̄(s) = E_v f(x_s(v))`. -/
noncomputable def fbarS (c : Ret n) (s : ℝ) : ℝ :=
  ∫ v, fX c (xLat c s (unitF53 v)) ∂stdGauss (Fin (n - 1))

/-- `ω̄(s) = E_v ω(x_s(v))`. -/
noncomputable def wbarS (c : Ret n) (s : ℝ) : ℝ :=
  ∫ v, wX c (xLat c s (unitF53 v)) ∂stdGauss (Fin (n - 1))

lemma continuous_fX (c : Ret n) : Continuous (fX c) := by
  unfold fX
  exact (continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp (continuous_hid2 (A1 c) (A2 c))).mul continuous_const).div_const _

lemma continuous_wX (c : Ret n) : Continuous (wX c) := by
  unfold wX
  exact (continuous_normSq.comp (continuous_hid2 (A1 c) (A2 c))).div_const _

/-- `|f(x) − f(y)| ≤ |a₂(x) − a₂(y)|/√n`. -/
lemma fX_sub_le (hn : 1 ≤ n) (c : Ret n) (x y : Fin n → ℝ) :
    |fX c x - fX c y| ≤ √(normSq (hid2 (A1 c) (A2 c) x - hid2 (A1 c) (A2 c) y)) / √(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnR
  by_cases hb : normSq (bR c) = 0
  · unfold fX; rw [hb]; simp; positivity
  have hb0 : 0 < √(normSq (bR c)) :=
    Real.sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hb))
  have e : fX c x - fX c y = (∑ j, (hid2 (A1 c) (A2 c) x - hid2 (A1 c) (A2 c) y) j * bR c j) /
      (√(n : ℝ) * √(normSq (bR c))) := by
    unfold fX; rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1; refine Finset.sum_congr rfl fun j _ => by simp only [Pi.sub_apply]; ring
  rw [e, abs_div, abs_of_pos (mul_pos hsn hb0), div_le_div_iff₀ (mul_pos hsn hb0) hsn]
  have := BstLean.Part130.abs_dot_le (hid2 (A1 c) (A2 c) x - hid2 (A1 c) (A2 c) y) (bR c)
  calc _ ≤ √(normSq (hid2 (A1 c) (A2 c) x - hid2 (A1 c) (A2 c) y)) * √(normSq (bR c)) *
        √(n : ℝ) := mul_le_mul_of_nonneg_right this hsn.le
    _ = _ := by ring

/-- `|ω(x) − ω(y)| ≤ (|a₂(x)| + |a₂(y)|)|a₂(x) − a₂(y)|/n`. -/
lemma wX_sub_le (hn : 1 ≤ n) (c : Ret n) (x y : Fin n → ℝ) :
    |wX c x - wX c y| ≤ (√(normSq (hid2 (A1 c) (A2 c) x)) + √(normSq (hid2 (A1 c) (A2 c) y))) *
      √(normSq (hid2 (A1 c) (A2 c) x - hid2 (A1 c) (A2 c) y)) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set u := hid2 (A1 c) (A2 c) x
  set w := hid2 (A1 c) (A2 c) y
  have e : wX c x - wX c y = (∑ j, (u - w) j * (u + w) j) / n := by
    unfold wX normSq; rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1; refine Finset.sum_congr rfl fun j _ => by simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [e, abs_div, abs_of_pos hnR]
  refine div_le_div_of_nonneg_right ?_ hnR.le
  refine (BstLean.Part130.abs_dot_le _ _).trans ?_
  have hadd : √(normSq (u + w)) ≤ √(normSq u) + √(normSq w) := by
    rw [Real.sqrt_le_left (by positivity)]
    have hd := BstLean.Part130.abs_dot_le u w
    have e2 : normSq (u + w) = normSq u + 2 * ∑ j, u j * w j + normSq w := by
      unfold normSq; rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by simp only [Pi.add_apply]; ring
    rw [e2, add_sq, Real.sq_sqrt (normSq_nonneg _), Real.sq_sqrt (normSq_nonneg _)]
    nlinarith [le_abs_self (∑ j, u j * w j)]
  calc √(normSq (u - w)) * √(normSq (u + w)) ≤ √(normSq (u - w)) * (√(normSq u) + √(normSq w)) :=
        mul_le_mul_of_nonneg_left hadd (Real.sqrt_nonneg _)
    _ = _ := by ring

/-! ## The Lipschitz bounds of the latitude means -/

lemma hid2_zero' (c : Ret n) : hid2 (A1 c) (A2 c) 0 = 0 := by
  unfold hid2; rw [Matrix.mulVec_zero]
  have : reluV (0 : Fin (mA n) → ℝ) = 0 := by funext i; simp [reluV, relu]
  rw [this, Matrix.mulVec_zero]; funext i; simp [reluV, relu]

lemma normSq_xLat_le' (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) (v : Fin (n - 1) → ℝ) :
    normSq (xLat c s (unitF53 v)) ≤ 1 := BstLean.Part162.normSq_xLat_le hn c hs v

lemma sqrt_hid2_le (hn : 1 ≤ n) (c : Ret n) {O₁ O₂ : ℝ} (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO₁ : 0 ≤ O₁) (hO₂ : 0 ≤ O₂) {s : ℝ} (hs : s ^ 2 ≤ 1) (v : Fin (n - 1) → ℝ) :
    √(normSq (hid2 (A1 c) (A2 c) (xLat c s (unitF53 v)))) ≤ O₂ * O₁ := by
  rw [Real.sqrt_le_left (by positivity)]
  refine (hid2_le h1 h2 _).trans ?_
  have := normSq_xLat_le' hn c hs v
  have : O₁ ^ 2 * normSq (xLat c s (unitF53 v)) ≤ O₁ ^ 2 := by
    nlinarith [sq_nonneg O₁]
  nlinarith [sq_nonneg O₂]

lemma integrable_fX_lat (hn : 1 ≤ n) (c : Ret n) {O₁ O₂ : ℝ} (h1 : OpB (A1 c) O₁)
    (h2 : OpB (A2 c) O₂) (hO₁ : 0 ≤ O₁) (hO₂ : 0 ≤ O₂) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    Integrable (fun v => fX c (xLat c s (unitF53 v))) (stdGauss (Fin (n - 1))) := by
  refine Integrable.mono' (integrable_const (O₂ * O₁ / √(n : ℝ)))
    ((continuous_fX c).measurable.comp (BstLean.Part161.measurable_xLat_comp c measurable_const
      measurable_unitF)).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
  have h := fX_sub_le hn c (xLat c s (unitF53 v)) 0
  have e : fX c 0 = 0 := by unfold fX; rw [hid2_zero']; simp
  rw [e, sub_zero, hid2_zero', sub_zero] at h
  rw [Real.norm_eq_abs]
  exact h.trans (div_le_div_of_nonneg_right (sqrt_hid2_le hn c h1 h2 hO₁ hO₂ hs v)
    (Real.sqrt_nonneg _))

lemma integrable_wX_lat (hn : 1 ≤ n) (c : Ret n) {O₁ O₂ : ℝ} (h1 : OpB (A1 c) O₁)
    (h2 : OpB (A2 c) O₂) (hO₁ : 0 ≤ O₁) (hO₂ : 0 ≤ O₂) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    Integrable (fun v => wX c (xLat c s (unitF53 v))) (stdGauss (Fin (n - 1))) := by
  refine Integrable.mono' (integrable_const ((O₂ * O₁) ^ 2 / (n : ℝ)))
    ((continuous_wX c).measurable.comp (BstLean.Part161.measurable_xLat_comp c measurable_const
      measurable_unitF)).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs]
  unfold wX
  rw [abs_of_nonneg (div_nonneg (normSq_nonneg _) (Nat.cast_nonneg _))]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have h := sqrt_hid2_le hn c h1 h2 hO₁ hO₂ hs v
  have h0 := Real.sqrt_nonneg (normSq (hid2 (A1 c) (A2 c) (xLat c s (unitF53 v))))
  calc normSq (hid2 (A1 c) (A2 c) (xLat c s (unitF53 v)))
      = √(normSq (hid2 (A1 c) (A2 c) (xLat c s (unitF53 v)))) ^ 2 :=
        (Real.sq_sqrt (normSq_nonneg _)).symm
    _ ≤ (O₂ * O₁) ^ 2 := pow_le_pow_left₀ h0 h 2

/-- **The Lipschitz bound of `f̄`** along the meridian: `|f̄(s) − f̄(s')| ≤ Λ|s − s'|/(√n√q)`,
`Λ = O₂O₁`. -/
theorem fbar_lip (hn : 1 ≤ n) (c : Ret n) {O₁ O₂ : ℝ} (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO₁ : 0 ≤ O₁) (hO₂ : 0 ≤ O₂) {s s' q : ℝ} (hq : 0 < q) (hs : s ^ 2 ≤ 1 - q)
    (hs' : s' ^ 2 ≤ 1 - q) :
    |fbarS c s - fbarS c s'| ≤ O₂ * O₁ * |s - s'| / (√(n : ℝ) * √q) := by
  have hs1 : s ^ 2 ≤ 1 := by linarith
  have hs1' : s' ^ 2 ≤ 1 := by linarith
  unfold fbarS
  rw [← integral_sub (integrable_fX_lat hn c h1 h2 hO₁ hO₂ hs1)
    (integrable_fX_lat hn c h1 h2 hO₁ hO₂ hs1')]
  have hb := norm_integral_le_of_norm_le_const (μ := stdGauss (Fin (n - 1)))
    (f := fun v => fX c (xLat c s (unitF53 v)) - fX c (xLat c s' (unitF53 v)))
    (C := O₂ * O₁ * |s - s'| / (√(n : ℝ) * √q)) (Filter.Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs] at hb
    simpa using hb
  rw [Real.norm_eq_abs]
  refine (fX_sub_le hn c _ _).trans ?_
  have hx := xLat_sub_le hn c hq hs hs' v
  have hh := hid2_sub_le h1 h2 (xLat c s (unitF53 v)) (xLat c s' (unitF53 v))
  have hsq : √(normSq (hid2 (A1 c) (A2 c) (xLat c s (unitF53 v)) -
      hid2 (A1 c) (A2 c) (xLat c s' (unitF53 v)))) ≤ O₂ * O₁ * |s - s'| / √q := by
    rw [Real.sqrt_le_left (by positivity)]
    refine hh.trans ?_
    rw [div_pow, mul_pow, mul_pow, sq_abs, Real.sq_sqrt hq.le]
    calc O₂ ^ 2 * (O₁ ^ 2 * normSq (xLat c s (unitF53 v) - xLat c s' (unitF53 v)))
        ≤ O₂ ^ 2 * (O₁ ^ 2 * ((s - s') ^ 2 / q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (sq_nonneg _)) (sq_nonneg _)
      _ = O₂ ^ 2 * O₁ ^ 2 * (s - s') ^ 2 / q := by ring
  calc _ ≤ O₂ * O₁ * |s - s'| / √q / √(n : ℝ) :=
        div_le_div_of_nonneg_right hsq (Real.sqrt_nonneg _)
    _ = _ := by rw [div_div, mul_comm √q]

/-- **The Lipschitz bound of `ω̄`**: `|ω̄(s) − ω̄(s')| ≤ 2Λ²|s − s'|/(n√q)`. -/
theorem wbar_lip (hn : 1 ≤ n) (c : Ret n) {O₁ O₂ : ℝ} (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO₁ : 0 ≤ O₁) (hO₂ : 0 ≤ O₂) {s s' q : ℝ} (hq : 0 < q) (hs : s ^ 2 ≤ 1 - q)
    (hs' : s' ^ 2 ≤ 1 - q) :
    |wbarS c s - wbarS c s'| ≤ 2 * (O₂ * O₁) ^ 2 * |s - s'| / (n * √q) := by
  have hs1 : s ^ 2 ≤ 1 := by linarith
  have hs1' : s' ^ 2 ≤ 1 := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold wbarS
  rw [← integral_sub (integrable_wX_lat hn c h1 h2 hO₁ hO₂ hs1)
    (integrable_wX_lat hn c h1 h2 hO₁ hO₂ hs1')]
  have hb := norm_integral_le_of_norm_le_const (μ := stdGauss (Fin (n - 1)))
    (f := fun v => wX c (xLat c s (unitF53 v)) - wX c (xLat c s' (unitF53 v)))
    (C := 2 * (O₂ * O₁) ^ 2 * |s - s'| / (n * √q)) (Filter.Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs] at hb
    simpa using hb
  rw [Real.norm_eq_abs]
  refine (wX_sub_le hn c _ _).trans ?_
  have hx := xLat_sub_le hn c hq hs hs' v
  have hh := hid2_sub_le h1 h2 (xLat c s (unitF53 v)) (xLat c s' (unitF53 v))
  have hsq : √(normSq (hid2 (A1 c) (A2 c) (xLat c s (unitF53 v)) -
      hid2 (A1 c) (A2 c) (xLat c s' (unitF53 v)))) ≤ O₂ * O₁ * |s - s'| / √q := by
    rw [Real.sqrt_le_left (by positivity)]
    refine hh.trans ?_
    rw [div_pow, mul_pow, mul_pow, sq_abs, Real.sq_sqrt hq.le]
    calc O₂ ^ 2 * (O₁ ^ 2 * normSq (xLat c s (unitF53 v) - xLat c s' (unitF53 v)))
        ≤ O₂ ^ 2 * (O₁ ^ 2 * ((s - s') ^ 2 / q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (sq_nonneg _)) (sq_nonneg _)
      _ = O₂ ^ 2 * O₁ ^ 2 * (s - s') ^ 2 / q := by ring
  have ha := sqrt_hid2_le hn c h1 h2 hO₁ hO₂ hs1 v
  have ha' := sqrt_hid2_le hn c h1 h2 hO₁ hO₂ hs1' v
  have hsum : √(normSq (hid2 (A1 c) (A2 c) (xLat c s (unitF53 v)))) +
      √(normSq (hid2 (A1 c) (A2 c) (xLat c s' (unitF53 v)))) ≤ 2 * (O₂ * O₁) := by linarith
  calc _ ≤ 2 * (O₂ * O₁) * (O₂ * O₁ * |s - s'| / √q) / n := by
        refine div_le_div_of_nonneg_right ?_ hnR.le
        exact mul_le_mul hsum hsq (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by field_simp

/-! ## The grid error on the kept indices -/

/-- `f̄` of Part 169 (`fbR`) is `fbarS` at the latitude of the index. -/
lemma fbR_eq (c : Ret n) (a : Ix n) : fbR c a = fbarS c (latC (paperDesignP n) c a) := by
  unfold fbR fbarS lbar
  rw [← integral_const_mul]
  congr 1; funext v
  show √(eR c) * lamX (paperDesignP n) c _ = fX c _
  unfold lamX fX lam eR
  rw [paperDesignP_bA]
  by_cases hb : normSq (bR c) = 0
  · rw [hb]; simp
  have hb0 : 0 < normSq (bR c) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hb)
  rw [Real.sqrt_div' _ (Nat.cast_nonneg n)]
  have h1 : √(normSq (bR c)) ^ 2 = normSq (bR c) := Real.sq_sqrt hb0.le
  have h2 : 0 < √(normSq (bR c)) := Real.sqrt_pos.mpr hb0
  field_simp
  rw [h1]
  ring

lemma wbR_eq (c : Ret n) (a : Ix n) : wbR c a = wbarS c (latC (paperDesignP n) c a) := rfl

lemma bulkI_eq (c : Ret n) : bulkI (paperDesignP n) c = Set.Icc (nodeL c) (nodeH c) := rfl

lemma lat_mem_of_KR {c : Ret n} {a : Ix n} (ha : a ∈ KR c) :
    nodeL c ≤ latC (paperDesignP n) c a ∧ latC (paperDesignP n) c a ≤ nodeH c := by
  have h : latC (paperDesignP n) c a ∈ bulkI (paperDesignP n) c := ha.1
  rw [bulkI_eq] at h
  exact h

lemma nodeS_mem (c : Ret n) (hLH : nodeL c < nodeH c) {g : ℕ} (hg : g < Js n) :
    nodeL c ≤ nodeS c g ∧ nodeS c g ≤ nodeH c := by
  have hJ : (0 : ℝ) < Js n := by exact_mod_cast (show 0 < Js n by omega)
  have hD : 0 < nodeD c := div_pos (by linarith) hJ
  have hgJ : (g : ℝ) + 1 ≤ Js n := by exact_mod_cast hg
  unfold nodeS
  constructor
  · have : 0 ≤ ((g : ℝ) + 1 / 2) * nodeD c := by positivity
    linarith
  · have e : nodeD c * (Js n : ℝ) = nodeH c - nodeL c := by unfold nodeD; field_simp
    nlinarith

/-- **The location grid error** (paper `t7:p08:grid`): on a kept index,
`|f̄(s) − f̄(s_g)| ≤ ΛΔ/(2√n√q)` when `s² ≤ 1 − q` on `[L, H]`. -/
theorem grid_f (hn : 1 ≤ n) (c : Ret n) {O₁ O₂ : ℝ} (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO₁ : 0 ≤ O₁) (hO₂ : 0 ≤ O₂) {q : ℝ} (hq : 0 < q) (hLH : nodeL c < nodeH c)
    (hbulk : ∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - q) {a : Ix n} (ha : a ∈ KR c) :
    |fbR c a - fbarS c (nodeS c (gIdx c (latC (paperDesignP n) c a)))| ≤
      O₂ * O₁ * (nodeD c / 2) / (√(n : ℝ) * √q) := by
  obtain ⟨hl1, hl2⟩ := lat_mem_of_KR ha
  obtain ⟨hnear, hg⟩ := gIdx_near hn c hLH hl1 hl2
  obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH hg
  rw [fbR_eq]
  refine (fbar_lip hn c h1 h2 hO₁ hO₂ hq (hbulk _ hl1 hl2) (hbulk _ hs1 hs2)).trans ?_
  have hpos : 0 < √(n : ℝ) * √q :=
    mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))) (Real.sqrt_pos.mpr hq)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnear (by positivity)) hpos.le

/-- **The energy grid error** (paper `t7:p08:grid`): on a kept index,
`|ω̄(s) − ω̄(s_g)| ≤ Λ²Δ/(n√q)`. -/
theorem grid_w (hn : 1 ≤ n) (c : Ret n) {O₁ O₂ : ℝ} (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO₁ : 0 ≤ O₁) (hO₂ : 0 ≤ O₂) {q : ℝ} (hq : 0 < q) (hLH : nodeL c < nodeH c)
    (hbulk : ∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - q) {a : Ix n} (ha : a ∈ KR c) :
    |wbR c a - wbarS c (nodeS c (gIdx c (latC (paperDesignP n) c a)))| ≤
      2 * (O₂ * O₁) ^ 2 * (nodeD c / 2) / (n * √q) := by
  obtain ⟨hl1, hl2⟩ := lat_mem_of_KR ha
  obtain ⟨hnear, hg⟩ := gIdx_near hn c hLH hl1 hl2
  obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH hg
  rw [wbR_eq]
  refine (wbar_lip hn c h1 h2 hO₁ hO₂ hq (hbulk _ hl1 hl2) (hbulk _ hs1 hs2)).trans ?_
  have hpos : 0 < (n : ℝ) * √q :=
    mul_pos (by exact_mod_cast (show 0 < n by omega)) (Real.sqrt_pos.mpr hq)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnear (by positivity)) hpos.le

end BstLean.Part169
