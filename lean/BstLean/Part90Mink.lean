import Mathlib

/-!
# Part 90: the Minkowski inequality for integer exponents, in integral form

`mink2`: for nonnegative `f`, `g` with `∫ f^n ≤ A^n`, `∫ g^n ≤ B^n`: `∫ (f + g)^n ≤ (A + B)^n`.
`mink3`: the same for three functions.

Proof: for `A, B > 0` and `λ = A/(A+B)`, convexity of `t ↦ t^n` gives pointwise
`(f + g)^n ≤ λ (f/λ)^n + (1 − λ) (g/(1 − λ))^n`. Zero bounds: replace `A, B` by `A + ε`, `B + ε`.
-/

namespace BstLean.Part90

open MeasureTheory

private lemma conv_pt (n : ℕ) (f g lam : ℝ) (hf : 0 ≤ f) (hg : 0 ≤ g) (h0 : 0 < lam)
    (h1 : lam < 1) :
    (f + g) ^ n ≤ lam * (f / lam) ^ n + (1 - lam) * (g / (1 - lam)) ^ n := by
  have h1' : 0 < 1 - lam := by linarith
  have hc := (convexOn_pow n).2 (x := f / lam) (y := g / (1 - lam))
    (Set.mem_Ici.mpr (div_nonneg hf h0.le)) (Set.mem_Ici.mpr (div_nonneg hg h1'.le))
    h0.le h1'.le (by ring)
  simp only [smul_eq_mul] at hc
  have e : lam * (f / lam) + (1 - lam) * (g / (1 - lam)) = f + g := by
    field_simp
  rw [e] at hc
  exact hc

private lemma int_add_pow {X : Type*} [MeasurableSpace X] {μ : Measure X} (n : ℕ) (f g : X → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hfi : Integrable (fun x => f x ^ n) μ) (hgi : Integrable (fun x => g x ^ n) μ) :
    Integrable (fun x => (f x + g x) ^ n) μ := by
  have hdom : Integrable (fun x => (1 / 2 : ℝ) * (f x / (1 / 2)) ^ n +
      (1 - 1 / 2) * (g x / (1 - 1 / 2)) ^ n) μ := by
    have e1 : (fun x => (1 / 2 : ℝ) * (f x / (1 / 2)) ^ n) =
        fun x => (1 / 2 * (1 / (1 / 2 : ℝ)) ^ n) * f x ^ n := by
      funext x; simp only [div_pow, one_pow]; ring
    have e2 : (fun x => (1 - 1 / 2 : ℝ) * (g x / (1 - 1 / 2)) ^ n) =
        fun x => ((1 - 1 / 2) * (1 / (1 - 1 / 2 : ℝ)) ^ n) * g x ^ n := by
      funext x; simp only [div_pow, one_pow]; ring
    have := (hfi.const_mul (1 / 2 * (1 / (1 / 2 : ℝ)) ^ n)).add
      (hgi.const_mul ((1 - 1 / 2) * (1 / (1 - 1 / 2 : ℝ)) ^ n))
    rw [← e1, ← e2] at this
    exact this
  refine hdom.mono' ((hfm.add hgm).pow n) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (add_nonneg (hf0 x) (hg0 x)) n)]
  exact conv_pt n (f x) (g x) (1 / 2) (hf0 x) (hg0 x) (by norm_num) (by norm_num)

private lemma mink2_pos {X : Type*} [MeasurableSpace X] {μ : Measure X} (n : ℕ) (hn : 1 ≤ n)
    (f g : X → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hfi : Integrable (fun x => f x ^ n) μ) (hgi : Integrable (fun x => g x ^ n) μ)
    (A B : ℝ) (hA0 : 0 < A) (hB0 : 0 < B)
    (hA : ∫ x, f x ^ n ∂μ ≤ A ^ n) (hB : ∫ x, g x ^ n ∂μ ≤ B ^ n) :
    ∫ x, (f x + g x) ^ n ∂μ ≤ (A + B) ^ n := by
  have hAB : 0 < A + B := by linarith
  set lam : ℝ := A / (A + B) with hlam
  have hl0 : 0 < lam := div_pos hA0 hAB
  have hl1 : lam < 1 := by rw [hlam, div_lt_one hAB]; linarith
  have hl1' : 1 - lam = B / (A + B) := by rw [hlam]; field_simp; ring
  have hl1p : 0 < 1 - lam := by linarith
  have e1 : (fun x => lam * (f x / lam) ^ n) = fun x => (lam * (1 / lam) ^ n) * f x ^ n := by
    funext x; simp only [div_pow, one_pow]; ring
  have e2 : (fun x => (1 - lam) * (g x / (1 - lam)) ^ n) =
      fun x => ((1 - lam) * (1 / (1 - lam)) ^ n) * g x ^ n := by
    funext x; simp only [div_pow, one_pow]; ring
  have hi1 : Integrable (fun x => lam * (f x / lam) ^ n) μ := by
    rw [e1]; exact hfi.const_mul _
  have hi2 : Integrable (fun x => (1 - lam) * (g x / (1 - lam)) ^ n) μ := by
    rw [e2]; exact hgi.const_mul _
  have hmono := integral_mono (int_add_pow n f g hf0 hg0 hfm hgm hfi hgi) (hi1.add hi2)
    (fun x => conv_pt n (f x) (g x) lam (hf0 x) (hg0 x) hl0 hl1)
  refine hmono.trans ?_
  rw [integral_add' hi1 hi2, e1, e2, integral_const_mul, integral_const_mul]
  have c1 : 0 ≤ lam * (1 / lam) ^ n := by positivity
  have c2 : 0 ≤ (1 - lam) * (1 / (1 - lam)) ^ n := by positivity
  have b1 := mul_le_mul_of_nonneg_left hA c1
  have b2 := mul_le_mul_of_nonneg_left hB c2
  have k1 : lam * (1 / lam) ^ n * A ^ n = lam * (A + B) ^ n := by
    rw [mul_assoc, ← mul_pow]
    congr 2
    rw [hlam]; field_simp
  have k2 : (1 - lam) * (1 / (1 - lam)) ^ n * B ^ n = (1 - lam) * (A + B) ^ n := by
    rw [mul_assoc, ← mul_pow]
    congr 2
    rw [hl1']; field_simp
  rw [k1] at b1
  rw [k2] at b2
  linarith

/-- **Minkowski's inequality** for a natural exponent, in integral form. -/
theorem mink2 {X : Type*} [MeasurableSpace X] {μ : Measure X} (n : ℕ) (hn : 1 ≤ n) (f g : X → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hfi : Integrable (fun x => f x ^ n) μ) (hgi : Integrable (fun x => g x ^ n) μ)
    (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∫ x, f x ^ n ∂μ ≤ A ^ n) (hB : ∫ x, g x ^ n ∂μ ≤ B ^ n) :
    Integrable (fun x => (f x + g x) ^ n) μ ∧ ∫ x, (f x + g x) ^ n ∂μ ≤ (A + B) ^ n := by
  refine ⟨int_add_pow n f g hf0 hg0 hfm hgm hfi hgi, ?_⟩
  have hev : ∀ ε : ℝ, 0 < ε → ∫ x, (f x + g x) ^ n ∂μ ≤ (A + ε + (B + ε)) ^ n := by
    intro ε hε
    refine mink2_pos n hn f g hf0 hg0 hfm hgm hfi hgi (A + ε) (B + ε) (by linarith) (by linarith)
      (hA.trans (pow_le_pow_left₀ hA0 (by linarith) n))
      (hB.trans (pow_le_pow_left₀ hB0 (by linarith) n))
  have hcont : Continuous fun ε : ℝ => (A + ε + (B + ε)) ^ n := by fun_prop
  have htend : Filter.Tendsto (fun ε : ℝ => (A + ε + (B + ε)) ^ n) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((A + 0 + (B + 0)) ^ n)) := (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have := ge_of_tendsto htend (Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => hev ε hε)
  simpa using this

/-- Minkowski's inequality for three functions. -/
theorem mink3 {X : Type*} [MeasurableSpace X] {μ : Measure X} (n : ℕ) (hn : 1 ≤ n)
    (f g h : X → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hhm : AEStronglyMeasurable h μ)
    (hfi : Integrable (fun x => f x ^ n) μ) (hgi : Integrable (fun x => g x ^ n) μ)
    (hhi : Integrable (fun x => h x ^ n) μ)
    (A B C : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hA : ∫ x, f x ^ n ∂μ ≤ A ^ n) (hB : ∫ x, g x ^ n ∂μ ≤ B ^ n)
    (hC : ∫ x, h x ^ n ∂μ ≤ C ^ n) :
    Integrable (fun x => (f x + g x + h x) ^ n) μ ∧
      ∫ x, (f x + g x + h x) ^ n ∂μ ≤ (A + B + C) ^ n := by
  obtain ⟨i1, b1⟩ := mink2 n hn f g hf0 hg0 hfm hgm hfi hgi A B hA0 hB0 hA hB
  exact mink2 n hn (fun x => f x + g x) h (fun x => add_nonneg (hf0 x) (hg0 x)) hh0
    (hfm.add hgm) hhm i1 hhi (A + B) C (add_nonneg hA0 hB0) hC0 b1 hC

end BstLean.Part90

#print axioms BstLean.Part90.mink2
#print axioms BstLean.Part90.mink3
