import BstLean.Part171Gen

/-!
# Part 171 (file `Var`): `V2N` and `piN` through the centred moments of `wT` (Part F1)

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, `E_v(v_v − ς²)² = V₂ = v_ε + h_U²` and "`π_g` ... Markov of order
eight bound it by the eighth power of that centred norm divided by `ς²/2 − 2ℓ_s²`".

* `int_wT_eq`: `E_v wT = ς² − DstN` (on `‖A₁‖_op ≤ O`).
* **`V2N_eq`**: `V2N = E_v(wT − E_v wT)² + DstN²` (the paper's `V₂ = v_ε + h_U²`).
* **`piN_le`**: if `DstN < ς²/2`, then `piN ≤ E_v(wT − E_v wT)⁸ / (ς²/2 − DstN)⁸`.
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part134 (res)
open BstLean.Part167 (perp)
open BstLean.Part170 (hB tA aLat aLat_normSq_le measurable_aLat aLat_bdd)

variable {n : ℕ}

lemma wT_nonneg (c : Ret n) (g : ℕ) (v : Fin (n - 1) → ℝ) : 0 ≤ wT c g v := by
  unfold wT; exact mul_nonneg (tA_nonneg n) (normSq_nonneg' _)

lemma wT_le (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (h1 : OpB (A1 c) O) (v : Fin (n - 1) → ℝ) : wT c g v ≤ tA n * O ^ 2 := by
  unfold wT
  exact mul_le_mul_of_nonneg_left ((BstLean.Part167.normSq_perp_le _ _).trans
    ((BstLean.Part167.normSq_perp_le _ _).trans (aLat_normSq_le hn c hs h1 v))) (tA_nonneg n)

lemma int_wT (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (h1 : OpB (A1 c) O) : Integrable (wT c g) (stdGauss (Fin (n - 1))) :=
  bdd_int (measurable_wT c g) (C := tA n * O ^ 2) fun v => by
    rw [abs_of_nonneg (wT_nonneg c g v)]; exact wT_le hn c g hs h1 v

/-- `E_v wT = ς² − DstN`. -/
lemma int_wT_eq (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) :
    ∫ v, wT c g v ∂stdGauss (Fin (n - 1)) = vsig2 c (nodeS c g) - DstN c g := by
  have hU := hUN_eq_DstN hn c g hs hO h1
  have iw := int_wT hn c g hs h1
  -- hUN = |E wT − ς²| and E wT ≤ ς²
  have hle : ∫ v, wT c g v ∂stdGauss (Fin (n - 1)) ≤ vsig2 c (nodeS c g) := by
    rw [vsig2_eq hn c hs hO h1]
    have hpt : ∀ v, wT c g v ≤ tA n * normSq (aLat c (nodeS c g) v - a1Bar c (nodeS c g)) := by
      intro v
      have hp := pyth c g (aLat c (nodeS c g) v - a1Bar c (nodeS c g))
      have e : perp (res (hB c) (a1Bar c (nodeS c g))) (perp (hB c)
          (aLat c (nodeS c g) v - a1Bar c (nodeS c g))) =
          perp (res (hB c) (a1Bar c (nodeS c g))) (perp (hB c) (aLat c (nodeS c g) v)) := by
        rw [perp_sub', perp_sub', BstLean.Part170.perp_perp_res, sub_zero]
      rw [e] at hp
      unfold wT
      nlinarith [sq_nonneg (q1 c (aLat c (nodeS c g) v - a1Bar c (nodeS c g))),
        sq_nonneg (q2 c g (aLat c (nodeS c g) v - a1Bar c (nodeS c g)))]
    rw [← integral_const_mul]
    exact integral_mono iw ((int_normSq_dev hn c hs hO h1).const_mul _) hpt
  unfold hUN at hU
  rw [integral_sub iw (integrable_const _)] at hU
  simp only [integral_const, probReal_univ, one_smul] at hU
  rw [abs_of_nonpos (by linarith)] at hU
  linarith

/-- **`V2N = E_v(wT − E_v wT)² + DstN²`** (the paper's `V₂ = v_ε + h_U²`). -/
theorem V2N_eq (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) :
    V2N c g = ∫ v, (wT c g v - ∫ w, wT c g w ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1)) + DstN c g ^ 2 := by
  have iw := int_wT hn c g hs h1
  have he := int_wT_eq hn c g hs hO h1
  set m := ∫ w, wT c g w ∂stdGauss (Fin (n - 1))
  have iw2 : Integrable (fun v => wT c g v ^ 2) (stdGauss (Fin (n - 1))) :=
    bdd_int ((measurable_wT c g).pow_const 2) (C := (tA n * O ^ 2) ^ 2) fun v =>
      sq_abs_le (by rw [abs_of_nonneg (wT_nonneg c g v)]; exact wT_le hn c g hs h1 v)
  have key : ∀ a : ℝ, ∫ v, (wT c g v - a) ^ 2 ∂stdGauss (Fin (n - 1)) =
      ∫ v, wT c g v ^ 2 ∂stdGauss (Fin (n - 1)) - 2 * a * m + a ^ 2 := by
    intro a
    have e : ∀ v, (wT c g v - a) ^ 2 = wT c g v ^ 2 - 2 * a * wT c g v + a ^ 2 := fun v => by ring
    simp_rw [e]
    have j1 : Integrable (fun v => wT c g v ^ 2 - 2 * a * wT c g v) (stdGauss (Fin (n - 1))) :=
      iw2.sub (iw.const_mul _)
    rw [integral_add j1 (integrable_const _), integral_sub iw2 (iw.const_mul _), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    rfl
  unfold V2N
  rw [key, key, he]
  rw [he] at *
  ring

/-- **`π_g` by Markov of order eight**: if `DstN < ς²/2`, then
`piN ≤ E_v(wT − E_v wT)⁸ / (ς²/2 − DstN)⁸`. -/
theorem piN_le (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) (hD : DstN c g < vsig2 c (nodeS c g) / 2) :
    piN c g ≤ (∫ v, (wT c g v - ∫ w, wT c g w ∂stdGauss (Fin (n - 1))) ^ 8
      ∂stdGauss (Fin (n - 1))) / (vsig2 c (nodeS c g) / 2 - DstN c g) ^ 8 := by
  have he := int_wT_eq hn c g hs hO h1
  set m := ∫ w, wT c g w ∂stdGauss (Fin (n - 1))
  set δ := vsig2 c (nodeS c g) / 2 - DstN c g with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set f : (Fin (n - 1) → ℝ) → ℝ := fun v => (wT c g v - m) ^ 8 with hf
  have hf0 : ∀ v, 0 ≤ f v := fun v => by simp only [hf]; positivity
  have ifn : Integrable f (stdGauss (Fin (n - 1))) := by
    refine bdd_int (((measurable_wT c g).sub_const _).pow_const 8) (C := (tA n * O ^ 2 + |m|) ^ 8)
      fun v => ?_
    rw [abs_of_nonneg (hf0 v)]
    have h0 := wT_nonneg c g v
    have h2 := wT_le hn c g hs h1 v
    have h3 : |wT c g v - m| ≤ tA n * O ^ 2 + |m| := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg h0]; linarith
    calc (wT c g v - m) ^ 8 = |wT c g v - m| ^ 8 := by rw [Even.pow_abs (by decide)]
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h3 8
  have hM := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hf0) ifn (δ ^ 8)
  have hsub : {v | wT c g v < vsig2 c (nodeS c g) / 2} ⊆ {v | δ ^ 8 ≤ f v} := by
    intro v hv
    simp only [mem_ofPred_eq] at hv ⊢
    have h1' : δ ≤ m - wT c g v := by rw [hδ, he]; linarith
    have h2' : δ ^ 8 ≤ (m - wT c g v) ^ 8 := pow_le_pow_left₀ hδ0.le h1' 8
    simp only [hf]
    calc δ ^ 8 ≤ (m - wT c g v) ^ 8 := h2'
      _ = (wT c g v - m) ^ 8 := by ring
  have hmono : piN c g ≤ (stdGauss (Fin (n - 1))).real {v | δ ^ 8 ≤ f v} :=
    measureReal_mono hsub
  rw [le_div_iff₀ (by positivity)]
  calc piN c g * δ ^ 8 ≤ (stdGauss (Fin (n - 1))).real {v | δ ^ 8 ≤ f v} * δ ^ 8 := by gcongr
    _ = δ ^ 8 * (stdGauss (Fin (n - 1))).real {v | δ ^ 8 ≤ f v} := by ring
    _ ≤ ∫ v, f v ∂stdGauss (Fin (n - 1)) := hM

end BstLean.Part171
