import BstLean.Part169Comp
import BstLean.Part169End

/-!
# Part 169 (file `Red`): `BIASP` from the moment inputs of Part 08

No proof is left open; no `native_decide` or `axiom` is used.

For the paper's program `D = paperDesignP n`, the split data `dP c` and the kept indices
`K = keptIx D c (dP c)`, this file names the per-index quantities of Part 08 and proves that
`BIASP c` follows from the inputs and the moment bounds of Part 08 and the numerical
inequality `P_B ≤ 0.004295²`. This is the exact interface for the remaining parts of the
discharge (see the plan in the report).

* `eR c = |b|²/n` (`e_b`).
* `fbR c a = √e_b·λ̄(a)` (`f̄`), `ftR c a = f̃` at the node of the latitude of `a`,
  `wtR c a = ω̃` at that node, `wbR c a = E_v|a₂(x_v)|²/n` (`ω̄`).
* `VR c a = ω̄ − f̄² − S̄/γ_A` (`γ_A = 2/n`). With `S̄ = E_v S` and `S = γ_A(ω − f²)`
  (`sA_eq`), `VR = E_v f² − f̄² = Var_v f` once the integrals split; this identity is NOT used
  here and is a later input.
* `sA_eq`: pointwise `S(x) = σ(x)² = γ_A(ω(x) − f(x)²)` with `ω = |a₂|²/n`,
  `f = ⟨a₂, b⟩/(√n|b|)`, for `b ≠ 0`.
* **`biasP_of_inputs`**: the reduction.
-/

namespace BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (hellG2 keptIx latC muI BIAS_hyp lamX sigX xLat measurable_latC Ix
  measurableSet_bulkIx measurableSet_keptSet)
open BstLean.Part162 (lbar measurable_lbar)
open BstLean.Part53 (unitF53 measurable_unitF)

variable {n : ℕ}

/-- `e_b = |b|²/n`. -/
noncomputable def eR (c : Ret n) : ℝ := normSq (bR c) / (n : ℝ)

/-- `f̄(a) = √e_b·λ̄(a)`, the full latitude mean of `f = ⟨a₂, b⟩/(√n|b|)`. -/
noncomputable def fbR (c : Ret n) (a : Ix n) : ℝ := √(eR c) * lbar (paperDesignP n) c a

/-- `f̃` at the node of the latitude of the index `a`. -/
noncomputable def ftR (c : Ret n) (a : Ix n) : ℝ :=
  fPass c (nodeS c (gIdx c (latC (paperDesignP n) c a)))

/-- `ω̃` at the node of the latitude of the index `a`. -/
noncomputable def wtR (c : Ret n) (a : Ix n) : ℝ :=
  wPass c (nodeS c (gIdx c (latC (paperDesignP n) c a)))

/-- `ω̄(a) = E_v |a₂(x_v)|²/n`. -/
noncomputable def wbR (c : Ret n) (a : Ix n) : ℝ :=
  ∫ v, normSq (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP n) c a) (unitF53 v))) / (n : ℝ)
    ∂stdGauss (Fin (n - 1))

/-- `V(a) = ω̄ − f̄² − S̄/γ_A` (it equals `Var_v f`, see the file header). -/
noncomputable def VR (c : Ret n) (a : Ix n) : ℝ :=
  wbR c a - fbR c a ^ 2 - (dP c).Sb a / (2 / (n : ℝ))

/-- The kept indices of the paper's program. -/
def KR (c : Ret n) : Set (Ix n) := keptIx (paperDesignP n) c (dP c)

lemma measurableSet_KR (c : Ret n) : MeasurableSet (KR c) :=
  measurableSet_keptSet _ (dP c).mgood (measurableSet_bulkIx _ c) _

lemma measurable_fbR (c : Ret n) : Measurable (fbR c) :=
  (measurable_lbar _ c).const_mul _

lemma measurable_gIdx_lat (c : Ret n) :
    Measurable (fun a : Ix n => gIdx c (latC (paperDesignP n) c a)) :=
  measurable_nodeIdx_comp (Js n) measurable_const measurable_const (measurable_latC _ c)

lemma measurable_ftR (c : Ret n) : Measurable (ftR c) :=
  (measurable_from_nat (f := fun g : ℕ => fPass c (nodeS c g))).comp (measurable_gIdx_lat c)

lemma measurable_wtR (c : Ret n) : Measurable (wtR c) :=
  (measurable_from_nat (f := fun g : ℕ => wPass c (nodeS c g))).comp (measurable_gIdx_lat c)

lemma measurable_wbR (c : Ret n) : Measurable (wbR c) := by
  have h : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) =>
      normSq (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP n) c p.1) (unitF53 p.2))) /
        (n : ℝ)) :=
    ((continuous_normSq.measurable.comp
      ((BstLean.Part134.continuous_hid2 (A1 c) (A2 c)).measurable.comp
        (BstLean.Part161.measurable_xA _ c))).div_const _)
  exact measurable_int_dir h

lemma measurable_VR (c : Ret n) : Measurable (VR c) :=
  ((measurable_wbR c).sub ((measurable_fbR c).pow_const 2)).sub ((dP c).mSb.div_const _)

/-- **The paper's residual scale** `S = σ² = γ_A(ω − f²)`, with `ω = |h|²/n`,
`f = ⟨h, b⟩/(√n|b|)`, for `b ≠ 0` (`m_A = n²`, `γ_A = 2/n`). -/
theorem sA_eq (hn : 0 < n) {b h : Fin (mA n) → ℝ} (hb : normSq b ≠ 0) :
    sig (2 / (mA n : ℝ)) b h ^ 2 =
      2 / (n : ℝ) * (normSq h / n - ((∑ j, h j * b j) / (√(n : ℝ) * √(normSq b))) ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hb)
  unfold sig
  rw [mul_pow, Real.sq_sqrt (by unfold mA; positivity), Real.sq_sqrt (normSq_nonneg _),
    BstLean.Part136.normSq_res hb, div_pow, mul_pow, Real.sq_sqrt hnR.le, Real.sq_sqrt hb0.le]
  unfold mA
  push_cast
  field_simp

/-- **`BIASP` from the inputs and the moments of Part 08.** On the kept indices `K`:
`S̄ ≥ γ_A d` (`d ≥ 1/5`), `|c_A|² ≤ γ_A e_b nχ`, `|V| ≤ v_max`, the `L⁸` bounds `a_ω`, `a_f` on
`n(ω̄ − ω̃)`, `n(f̄ − f̃)`, the bounds `H_f` on `‖f̄‖_4`, `‖f̄‖_24`, the bound `C_v` on `‖nV‖_2`
(with the integrability of the functions involved), and the numerical inequality
`P_B ≤ 0.004295²`. -/
theorem biasP_of_inputs (hn : 0 < n) (c : Ret n) (he : 0 < eR c)
    {χ d ε vmax aw af Hf Cv : ℝ} (hd : 1 / 5 ≤ d) (hε1 : ε < 1) (hT : 0 < ε - vmax / d)
    (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hSbd : ∀ a ∈ KR c, 2 / (n : ℝ) * d ≤ (dP c).Sb a)
    (hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ)
    (hVm : ∀ a ∈ KR c, |VR c a| ≤ vmax)
    (iW2 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 2) (KR c) (muI n))
    (iW6 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 6) (KR c) (muI n))
    (iW8 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 8) (KR c) (muI n))
    (iF2 : IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 2) (KR c) (muI n))
    (iF4 : IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 4) (KR c) (muI n))
    (iF8 : IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 8) (KR c) (muI n))
    (if4 : IntegrableOn (fun a => fbR c a ^ 4) (KR c) (muI n))
    (if24 : IntegrableOn (fun a => fbR c a ^ 24) (KR c) (muI n))
    (ifF2 : IntegrableOn (fun a => fbR c a ^ 2 * ((n : ℝ) * (fbR c a - ftR c a)) ^ 2) (KR c)
      (muI n))
    (ifF6 : IntegrableOn (fun a => fbR c a ^ 6 * ((n : ℝ) * (fbR c a - ftR c a)) ^ 6) (KR c)
      (muI n))
    (iV : IntegrableOn (fun a => ((n : ℝ) * VR c a) ^ 2) (KR c) (muI n))
    (hW8 : ∫ a in KR c, ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤ aw ^ 8)
    (hF8 : ∫ a in KR c, ((n : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI n ≤ af ^ 8)
    (hf4 : ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ Hf ^ 4)
    (hf24 : ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ Hf ^ 24)
    (hV : ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ Cv ^ 2)
    (hnum : PB n χ d ε vmax aw af Hf Cv ≤ (4295 / 10 ^ 6) ^ 2) :
    BIASP c := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have hse : 0 < √(eR c) := Real.sqrt_pos.mpr he
  -- the integrand of `BIAS_hyp` in the abstract form
  have hS : ∀ a, (dP c).Sb a = 2 / (n : ℝ) * (wbR c a - fbR c a ^ 2 - VR c a) := by
    intro a; unfold VR; field_simp; ring
  have hfun : (fun a => hellG2 n (((dP c).lamb a -
        ((paperDesignP n).mix c (latC (paperDesignP n) c a)).1) ^ 2 * normSq c.2.1.2)
        ((dP c).Sb a) ((paperDesignP n).mix c (latC (paperDesignP n) c a)).2) =
      fun a => hellG2 n ((fbR c a / √(eR c) - ftR c a / √(eR c)) ^ 2 * normSq c.2.1.2)
        (2 / (n : ℝ) * (wbR c a - fbR c a ^ 2 - VR c a))
        (2 / (n : ℝ) * max (1 / 5) (wtR c a - ftR c a ^ 2)) := by
    funext a
    rw [← hS a, mixP_eq]
    have e1 : (dP c).lamb a = fbR c a / √(eR c) := by
      unfold fbR; field_simp; rfl
    rw [e1]
    rfl
  have hint := bias_price_paper (muI n) (measurableSet_KR c)
    (by have := measureReal_le_one (μ := muI n) (s := KR c); exact this) n hn hγ he hd
    (normSq_nonneg _) hc hε1 hT haw haf hHf hCv (measurable_fbR c) (measurable_ftR c)
    (measurable_wbR c) (measurable_wtR c) (measurable_VR c)
    (fun a ha => (hS a) ▸ hSbd a ha) hVm iW2 iW6 iW8 iF2 iF4 iF8 if4 if24 ifF2 ifF6 iV
    hW8 hF8 hf4 hf24 hV
  unfold BIASP BIAS_hyp
  have hle : ∫ a in keptIx (paperDesignP n) c (dP c), hellG2 n (((dP c).lamb a -
        ((paperDesignP n).mix c (latC (paperDesignP n) c a)).1) ^ 2 * normSq c.2.1.2)
        ((dP c).Sb a) ((paperDesignP n).mix c (latC (paperDesignP n) c a)).2 ∂muI n ≤
      (4295 / 10 ^ 6) ^ 2 := by
    rw [hfun]; exact hint.trans hnum
  calc _ ≤ √((4295 / 10 ^ 6 : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
    _ = 4295 / 10 ^ 6 := Real.sqrt_sq (by norm_num)

end BstLean.Part169
