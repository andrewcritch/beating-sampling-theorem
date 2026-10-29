import BstLean.Part144Struct2
import BstLean.Part144LipT

/-!
# Part 144, the conditional step with no event on `τ`

Role: `delegations/statements/p144-spec.md`, item 2. The polynomial lower bound of the
conditional failure probability (the tangent form `fail_cond2` and `lip_lower`) for every
`(W, A, F₁, F₂)` with `0 < τ ≤ 2c`, and its mean over the inputs with the three parts of
`E_{u,u′}(kD − c)²` kept apart (`lipMeanT_ge` of `Part144LipT`).

* `xR_second_exact`: `E_us (X − c)² = (τ − c)² + (2/k)·x₂ + (2(k − 1)/k)·f²`.
* `cond_lipT`: the pointwise lower bound, a polynomial in `X` and `w`.
* `lip_intT`: `max(0, E_us (lower bound)) ≥ (A − b) − C_m·QD/c²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
  BstLean.Part142

variable {N mW n mA mF : ℕ}

section fixed

variable (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N mW n) (A : MlpParam n mA n)
  (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)

include hn hN in
/-- **The exact second moment of `X` over the inputs**: with `x₂ = α²·Var(|z − m|²)/2 ≥ 0`:
`E_us (X − c)² = (τ − c)² + (2/k)·x₂ + (2(k − 1)/k)·f²`, and
`(τ − c)² + x₂ + f² ≤ E_{u,u′}(kD − c)²`. -/
lemma xR_second_exact (hmF : 1 ≤ mF) {k : ℕ} (hk : 1 ≤ k) (A' : MlpParam n mA n)
    (F₃ : Matrix (Fin 1) (Fin mF) ℝ) (c : ℝ) :
    ∃ x2 : ℝ, 0 ≤ x2 ∧
      ∫ us, (xR k W A F₁ F₂ us - c) ^ 2 ∂uniK k N =
        (tauR W A F₁ F₂ - c) ^ 2 + 2 / (k : ℝ) * x2 +
          2 * ((k : ℝ) - 1) / (k : ℝ) * fR W A F₁ F₂ ^ 2 ∧
      (tauR W A F₁ F₂ - c) ^ 2 + x2 + fR W A F₁ F₂ ^ 2 ≤
        QD c ((W, A, A', F₁, F₂, F₃) : Rest N mW n mA mF) := by
  have := uniformSphere_isProbability N hN
  have := uniK_prob hN k
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hm : (0 : ℝ) < mF := by exact_mod_cast hmF
  set α : ℝ := 2 / (mF : ℝ) with hα
  have hα0 : 0 < α := by positivity
  set z := zU W A F₁ F₂ with hz
  have hzm := zU_meas W A F₁ F₂
  have hzb := zU_bdd hn W A F₁ F₂
  set τ := tauR W A F₁ F₂ with hτ
  set f := fR W A F₁ F₂ with hf
  set T := trC (uniformSphere N) z with hT
  set Rv := radV (uniformSphere N) z with hRv
  set Φ := frC (uniformSphere N) z with hΦ
  have hΦ0 : 0 ≤ Φ := by
    rw [hΦ]; unfold frC
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hRv0 : 0 ≤ Rv := by rw [hRv]; unfold radV; exact integral_nonneg fun _ => sq_nonneg _
  have hff : f ^ 2 = α ^ 2 * Φ := by
    rw [hf]; simp only [fR, ← hα, ← hz, ← hΦ]
    rw [mul_pow, Real.sq_sqrt hΦ0]
  have hτT : τ = α * T := rfl
  set G : (Fin k → Fin N → ℝ) → ℝ := fun us => sqS (uniformSphere N) z k us - k * T with hG
  have hsB : BM (sqS (uniformSphere N) z k) := sqS_bm (uniformSphere N) z hzm hzb k
  have hGB : BM G := hsB.sub (BM.const _)
  have hG1 : ∫ us, G us ∂uniK k N = 0 := by
    rw [hG, integral_sub (hsB.integrable _) (integrable_const _), uniK,
      sqS_mean (uniformSphere N) z hzm hzb k]
    simp [hT]
  have hG2 : ∫ us, G us ^ 2 ∂uniK k N = k * Rv + 2 * k * (k - 1) * Φ := by
    rw [hG, uniK]; exact sqS_var (uniformSphere N) z hzm hzb k
  set a : ℝ := α / k with ha
  have hX : ∀ us, xR k W A F₁ F₂ us = a * G us + τ := by
    intro us
    simp only [xR, ← hα, ← hz, hG, ha, hτT]
    field_simp
    ring
  have hXB : BM (fun us => xR k W A F₁ F₂ us) := by
    have e : (fun us => xR k W A F₁ F₂ us) = fun us => a * G us + τ := funext hX
    rw [e]; exact ((BM.const a).mul hGB).add (BM.const τ)
  have hQ := QD_ge hn hN W A F₁ F₂ hmF A' F₃ c
  simp only [← hα, ← hz, ← hτ, ← hf, ← hRv] at hQ
  refine ⟨α ^ 2 * Rv / 2, by positivity, ?_, hQ⟩
  have e : (fun us => (xR k W A F₁ F₂ us - c) ^ 2) =
      fun us => a ^ 2 * G us ^ 2 + 2 * a * (τ - c) * G us + (τ - c) ^ 2 := by
    funext us; rw [hX us]; ring
  have i1 : Integrable (fun us => a ^ 2 * G us ^ 2) (uniK k N) :=
    (hGB.sq.integrable _).const_mul _
  have i2 : Integrable (fun us => 2 * a * (τ - c) * G us) (uniK k N) :=
    (hGB.integrable _).const_mul _
  have i12 : Integrable (fun us => a ^ 2 * G us ^ 2 + 2 * a * (τ - c) * G us) (uniK k N) :=
    i1.add i2
  have e1 : ∫ us, (a ^ 2 * G us ^ 2 + 2 * a * (τ - c) * G us + (τ - c) ^ 2) ∂uniK k N =
      ∫ us, (a ^ 2 * G us ^ 2 + 2 * a * (τ - c) * G us) ∂uniK k N +
        ∫ _us, (τ - c) ^ 2 ∂uniK k N :=
    integral_add i12 (integrable_const _)
  have e2 : ∫ us, (a ^ 2 * G us ^ 2 + 2 * a * (τ - c) * G us) ∂uniK k N =
      ∫ us, a ^ 2 * G us ^ 2 ∂uniK k N + ∫ us, 2 * a * (τ - c) * G us ∂uniK k N :=
    integral_add i1 i2
  rw [e, e1, e2, integral_const_mul, integral_const_mul, hG1, hG2, integral_const]
  simp only [mul_zero, add_zero, probReal_univ, smul_eq_mul, one_mul]
  rw [hff, ha]
  field_simp
  ring

include hn hN in
/-- **The polynomial lower bound of the conditional failure probability.** With a lower bound
`Tl ≤ Φ̄(t0)`, `κ = φ(t0)/(2t0)`, `A = 2(Tl + κ·t0²)`, `b = 2κ·k/4`: if `0 < τ ≤ 2c`,
`2(Φ̄(t0) + κ·t0²) ≤ Φ̄(1)` and `k ≤ 4·t0²`, then for all inputs the conditional probability
(over `F₃`) of
`|ĝ_k − B| > sd/2` is at least
`(A − bτ/c) + (bτ/c²)(X − c) − (A/c²)(X − c)² − A³k²/(4(bτ)²)·w`. -/
theorem cond_lipT (hmF : 1 ≤ mF) {k : ℕ} (hk : 1 ≤ k) (us : Fin k → Fin N → ℝ) {t0 c Tl : ℝ}
    (ht0 : 0 < t0) (hc : 0 < c) (hTl0 : 0 ≤ Tl) (hTl : Tl ≤ (gaussianReal 0 1).real (Ioi t0))
    (hA1 : 2 * ((gaussianReal 0 1).real (Ioi t0) + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2) ≤
      (gaussianReal 0 1).real (Ioi 1))
    (hk4 : (k : ℝ) ≤ 4 * t0 ^ 2) (hτpos : 0 < tauR W A F₁ F₂) (hτhi : tauR W A F₁ F₂ ≤ 2 * c) :
    ((2 * (Tl + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2)) -
          2 * (gaussianPDFReal 0 1 t0 / (2 * t0) * ((k : ℝ) / 4)) * tauR W A F₁ F₂ / c) +
        2 * (gaussianPDFReal 0 1 t0 / (2 * t0) * ((k : ℝ) / 4)) * tauR W A F₁ F₂ / c ^ 2 *
          (xR k W A F₁ F₂ us - c) -
        (2 * (Tl + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2)) / c ^ 2 *
          (xR k W A F₁ F₂ us - c) ^ 2 -
        (2 * (Tl + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2)) ^ 3 * (k : ℝ) ^ 2 /
          (4 * (2 * (gaussianPDFReal 0 1 t0 / (2 * t0) * ((k : ℝ) / 4)) * tauR W A F₁ F₂) ^ 2) *
          wR k W A F₁ F₂ us ≤
      (gaussMat 1 mF (2 / (mF : ℝ))).real
        {F₃ | sdn W A (F₁, F₂, F₃) / 2 <
          |gMean k W A (F₁, F₂, F₃) us - Bn W A (F₁, F₂, F₃)|} := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  set κ : ℝ := gaussianPDFReal 0 1 t0 / (2 * t0) with hκ
  have hφ : 0 < gaussianPDFReal 0 1 t0 := by
    rw [BstLean.Part131.pdf_eq]; positivity
  have hκ0 : 0 < κ := by positivity
  set τ := tauR W A F₁ F₂ with hτd
  have hA : 0 < 2 * (Tl + κ * t0 ^ 2) := by positivity
  have hb0 : 0 < 2 * (κ * ((k : ℝ) / 4)) := by positivity
  have hB : 0 < 2 * (κ * ((k : ℝ) / 4)) * τ := mul_pos hb0 hτpos
  have hbA : 2 * (κ * ((k : ℝ) / 4)) ≤ 2 * (Tl + κ * t0 ^ 2) := by
    have : κ * ((k : ℝ) / 4) ≤ κ * t0 ^ 2 := mul_le_mul_of_nonneg_left (by linarith) hκ0.le
    linarith
  have hBA : 2 * (κ * ((k : ℝ) / 4)) * τ ≤ 2 * (2 * (Tl + κ * t0 ^ 2)) * c := by
    have h1 : 2 * (κ * ((k : ℝ) / 4)) * τ ≤ 2 * (κ * ((k : ℝ) / 4)) * (2 * c) :=
      mul_le_mul_of_nonneg_left hτhi hb0.le
    have h2 : 2 * (κ * ((k : ℝ) / 4)) * (2 * c) ≤ 2 * (Tl + κ * t0 ^ 2) * (2 * c) :=
      mul_le_mul_of_nonneg_right hbA (by positivity)
    linarith
  refine lip_lower hA hB hc hBA hk0 (xR_nonneg W A F₁ F₂ k us)
    (wR_nonneg hn hN W A F₁ F₂ k us) measureReal_nonneg ?_
  intro hX hV
  have h := fail_cond2 hn hN W A F₁ F₂ hmF hk us ht0 hA1 hX hV
  rw [← hκ, ← hτd] at h
  linarith

include hn hN in
/-- **The mean of the polynomial lower bound over the inputs, with no event on `τ`.** For
`0 < b ≤ A`, `τ > 0`, `k ≥ 2`, and `C_m`, `v₀` as in `lipMeanT_ge` (`Part144LipT`):
`max(0, E_us (lower bound)) ≥ (A − b) − C_m·QD/c²`. -/
theorem lip_intT (hmF : 1 ≤ mF) {k : ℕ} (hk : 2 ≤ k) (A' : MlpParam n mA n)
    (F₃ : Matrix (Fin 1) (Fin mF) ℝ) {Ac b c Cm v0 : ℝ} (hA : 0 < Ac) (hb : 0 < b) (hbA : b ≤ Ac)
    (hc : 0 < c) (hτ : 0 < tauR W A F₁ F₂)
    (hK1 : Ac - b ≤ Cm) (hK2 : 2 * Ac / (k : ℝ) ≤ Cm)
    (hKα : 2 * Ac * ((k : ℝ) - 1) / (k : ℝ) < Cm) (hv0 : 0 ≤ v0) (hv1 : v0 ≤ 1)
    (hav : (Ac - b) * (Cm - 2 * Ac * ((k : ℝ) - 1) / (k : ℝ)) ≤
      2 * (Ac ^ 3 * (k : ℝ) / (4 * b ^ 2)) * Cm * v0)
    (hβ : Ac ^ 3 * (k : ℝ) / (4 * b ^ 2) ≤
      (Cm - 2 * Ac * ((k : ℝ) - 1) / (k : ℝ)) * (1 - v0) ^ 2) :
    BM (fun us => (Ac - b * tauR W A F₁ F₂ / c) +
      b * tauR W A F₁ F₂ / c ^ 2 * (xR k W A F₁ F₂ us - c) -
      Ac / c ^ 2 * (xR k W A F₁ F₂ us - c) ^ 2 -
      Ac ^ 3 * (k : ℝ) ^ 2 / (4 * (b * tauR W A F₁ F₂) ^ 2) * wR k W A F₁ F₂ us) ∧
    (Ac - b) - Cm * QD c ((W, A, A', F₁, F₂, F₃) : Rest N mW n mA mF) / c ^ 2 ≤
      max 0 (∫ us, ((Ac - b * tauR W A F₁ F₂ / c) +
        b * tauR W A F₁ F₂ / c ^ 2 * (xR k W A F₁ F₂ us - c) -
        Ac / c ^ 2 * (xR k W A F₁ F₂ us - c) ^ 2 -
        Ac ^ 3 * (k : ℝ) ^ 2 / (4 * (b * tauR W A F₁ F₂) ^ 2) * wR k W A F₁ F₂ us) ∂uniK k N) := by
  have hk : 1 ≤ k := by omega
  have := uniK_prob hN k
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkR2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  have hk0 : (0 : ℝ) < k := by linarith
  obtain ⟨hXB, hX1, _, _⟩ := xR_moments hn hN W A F₁ F₂ hmF hk A' F₃ c
  obtain ⟨x2, hx20, hm2e, hQ⟩ := xR_second_exact hn hN W A F₁ F₂ hmF hk A' F₃ c
  obtain ⟨hwB, hw1⟩ := wR_mean hn hN W A F₁ F₂ hk
  set τ := tauR W A F₁ F₂ with hτd
  set f := fR W A F₁ F₂ with hf
  set X : (Fin k → Fin N → ℝ) → ℝ := fun us => xR k W A F₁ F₂ us with hXd
  set w : (Fin k → Fin N → ℝ) → ℝ := fun us => wR k W A F₁ F₂ us with hwd
  set Q := QD c ((W, A, A', F₁, F₂, F₃) : Rest N mW n mA mF) with hQd
  set m2 : ℝ := ∫ us, (X us - c) ^ 2 ∂uniK k N with hm2
  set C0 : ℝ := Ac - b * τ / c with hC0
  set C1 : ℝ := b * τ / c ^ 2 with hC1
  set C2 : ℝ := Ac / c ^ 2 with hC2
  set C3 : ℝ := Ac ^ 3 * (k : ℝ) ^ 2 / (4 * (b * τ) ^ 2) with hC3
  have hXcB : BM (fun us => X us - c) := hXB.sub (BM.const c)
  have hB : BM (fun us => C0 + C1 * (X us - c) - C2 * (X us - c) ^ 2 - C3 * w us) :=
    (((BM.const C0).add ((BM.const C1).mul hXcB)).sub ((BM.const C2).mul hXcB.sq)).sub
      ((BM.const C3).mul hwB)
  refine ⟨hB, ?_⟩
  have hint : ∫ us, (C0 + C1 * (X us - c) - C2 * (X us - c) ^ 2 - C3 * w us) ∂uniK k N =
      C0 + C1 * (τ - c) - C2 * m2 - C3 * (f ^ 2 / (k : ℝ)) := by
    have i0 : Integrable (fun _us : Fin k → Fin N → ℝ => C0) (uniK k N) := integrable_const _
    have i1 : Integrable (fun us => C1 * (X us - c)) (uniK k N) :=
      (hXcB.integrable _).const_mul _
    have i2 : Integrable (fun us => C2 * (X us - c) ^ 2) (uniK k N) :=
      (hXcB.sq.integrable _).const_mul _
    have i3 : Integrable (fun us => C3 * w us) (uniK k N) := (hwB.integrable _).const_mul _
    have e1 : ∫ us, (C0 + C1 * (X us - c) - C2 * (X us - c) ^ 2 - C3 * w us) ∂uniK k N =
        ∫ us, (C0 + C1 * (X us - c) - C2 * (X us - c) ^ 2) ∂uniK k N -
          ∫ us, C3 * w us ∂uniK k N := integral_sub ((i0.add i1).sub i2) i3
    have e2 : ∫ us, (C0 + C1 * (X us - c) - C2 * (X us - c) ^ 2) ∂uniK k N =
        ∫ us, (C0 + C1 * (X us - c)) ∂uniK k N - ∫ us, C2 * (X us - c) ^ 2 ∂uniK k N :=
      integral_sub (i0.add i1) i2
    have e3 : ∫ us, (C0 + C1 * (X us - c)) ∂uniK k N =
        ∫ _us, C0 ∂uniK k N + ∫ us, C1 * (X us - c) ∂uniK k N := integral_add i0 i1
    have e4 : ∫ us, (X us - c) ∂uniK k N = τ - c := by
      rw [integral_sub (hXB.integrable _) (integrable_const _), hX1, integral_const]
      simp
    rw [e1, e2, e3, integral_const_mul, integral_const_mul, integral_const_mul, e4, hw1,
      integral_const]
    simp [hm2]
  rw [hint]
  exact lipMeanT_ge (A := Ac) (b := b) (c := c) (τ := τ) (f := f) (kk := (k : ℝ))
    (m2 := m2) (x2 := x2) (Q := Q) (Cm := Cm) (v0 := v0) hA hb hbA hc hkR2 hτ hm2e hx20 hQ
    hK1 hK2 hKα hv0 hv1 hav hβ

end fixed

end BstLean.Part144

open BstLean.Part144 in
#print axioms xR_second_exact
open BstLean.Part144 in
#print axioms cond_lipT
open BstLean.Part144 in
#print axioms lip_intT
