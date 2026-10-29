import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.MeanInequalities

/-!
# Part 184 (file `Mom`): the eighth moment of a sum of independent centred rows

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, Lemma `t7:p08:BE` (Bernstein energy fluctuation) and Lemma
`t7:p08:RA` (the expansion of `E(Σ_j X_j)^p` for independent centred `X_j` has no singleton block).
Lean's form is the exact moment expansion at order eight, not a Bernstein tail.

* `Ek S k`: the moment–cumulant polynomials (`E₄ = 3S₂² + S₄`, …,
  `E₈ = 105S₂⁴ + 210S₂²S₄ + 280S₂S₃² + 35S₄² + 28S₂S₆ + 56S₃S₅ + S₈`); `Ek_step`: the binomial
  convolution with one more row is bounded by `Ek` of the summed moments.
* `Smom ρ φ k = Σ_j E|φ_j|^k`.
* `mom_all`: for independent rows (coordinates of `Measure.pi`) with `E φ_j = 0` and `E φ_j⁸ < ∞`:
  `|E(Σ_j φ_j)^k| ≤ E_k(S)` for every `k ≤ 8` (induction over the rows, `measurePreserving_piFinSuccAbove`).
* `int_cs2`, `Smom_cs`: Cauchy–Schwarz, `S_{a+b}² ≤ S_{2a}S_{2b}`.
* **`mom8_pi`**: `E(Σ_j φ_j)⁸ ≤ 105S₂⁴ + 490S₂²S₄ + 63S₄² + 56S₂S₆ + S₈`; `mom8_pi_lint` (lintegral form).
-/

namespace BstLean.Part184

/-- The moment–cumulant polynomials. -/
noncomputable def Ek (S : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => S 2
  | 3 => S 3
  | 4 => 3 * S 2 ^ 2 + S 4
  | 5 => 10 * S 2 * S 3 + S 5
  | 6 => 15 * S 2 ^ 3 + 15 * S 2 * S 4 + 10 * S 3 ^ 2 + S 6
  | 7 => 105 * S 2 ^ 2 * S 3 + 21 * S 2 * S 5 + 35 * S 3 * S 4 + S 7
  | 8 => 105 * S 2 ^ 4 + 210 * S 2 ^ 2 * S 4 + 280 * S 2 * S 3 ^ 2 + 35 * S 4 ^ 2 +
      28 * S 2 * S 6 + 56 * S 3 * S 5 + S 8
  | _ => 0

/-- The row weights: `1, 0, s₂, s₃, …`. -/
noncomputable def cw (s : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | k => s k

lemma Ek_step {k : ℕ} (hk : k ≤ 8) (S s : ℕ → ℝ) (hS : ∀ i, 0 ≤ S i) (hs : ∀ i, 0 ≤ s i) :
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * cw s i * Ek S (k - i) ≤ Ek (S + s) k := by
  lift S to ℕ → NNReal using hS
  lift s to ℕ → NNReal using hs
  interval_cases k <;>
    simp [Finset.sum_range_succ, Ek, cw, Nat.choose] <;>
    (rw [← sub_nonneg]; ring_nf; positivity)


lemma Ek_nonneg (k : ℕ) (S : ℕ → ℝ) (hS : ∀ i, 0 ≤ S i) : 0 ≤ Ek S k := by
  lift S to ℕ → NNReal using hS
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [Ek] <;> positivity

lemma cw_nonneg (i : ℕ) (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) : 0 ≤ cw s i := by
  rcases i with _ | _ | i <;> simp [cw, hs]

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] (ρ : Measure X)

/-- `S_k = Σ_j E|φ_j|^k`. -/
noncomputable def Smom {m : ℕ} (φ : Fin m → X → ℝ) (k : ℕ) : ℝ := ∑ j, ∫ x, |φ j x| ^ k ∂ρ

variable [IsProbabilityMeasure ρ]

lemma int_abs_pow_of_8 {f : X → ℝ} (hf : Measurable f) (hi : Integrable (fun x => f x ^ 8) ρ)
    {k : ℕ} (hk : k ≤ 8) : Integrable (fun x => |f x| ^ k) ρ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hi)
    (((continuous_abs.measurable.comp hf).pow_const k).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have e8 : f x ^ 8 = |f x| ^ 8 := (Even.pow_abs ⟨4, rfl⟩ _).symm
  simp only [Pi.add_apply]
  rw [e8]
  rcases le_total (|f x|) 1 with h | h
  · have : |f x| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) h
    have : 0 ≤ |f x| ^ 8 := by positivity
    linarith
  · have : |f x| ^ k ≤ |f x| ^ 8 := pow_le_pow_right₀ h hk
    linarith

lemma int_pow_of_8 {f : X → ℝ} (hf : Measurable f) (hi : Integrable (fun x => f x ^ 8) ρ)
    {k : ℕ} (hk : k ≤ 8) : Integrable (fun x => f x ^ k) ρ := by
  refine (int_abs_pow_of_8 ρ hf hi hk).mono' ((hf.pow_const k).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]

omit [IsProbabilityMeasure ρ] in
lemma Smom_nonneg {m : ℕ} (φ : Fin m → X → ℝ) (k : ℕ) : 0 ≤ Smom ρ φ k :=
  Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity

/-- **All moments up to order 8 of a sum of independent centred rows.** -/
theorem mom_all : ∀ (m : ℕ) (φ : Fin m → X → ℝ), (∀ j, Measurable (φ j)) →
    (∀ j, Integrable (fun x => φ j x ^ 8) ρ) → (∀ j, ∫ x, φ j x ∂ρ = 0) →
    ∀ k ≤ 8, Integrable (fun y : Fin m → X => (∑ j, φ j (y j)) ^ k) (Measure.pi fun _ => ρ) ∧
      |∫ y, (∑ j, φ j (y j)) ^ k ∂(Measure.pi fun _ => ρ)| ≤ Ek (Smom ρ φ) k := by
  intro m
  induction m with
  | zero =>
    intro φ _ _ _ k hk
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    refine ⟨integrable_const _, ?_⟩
    have hS : Smom ρ φ = fun _ => 0 := by funext i; simp [Smom]
    rw [hS]
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [Ek]
  | succ m ih =>
    intro φ hm hi h0 k hk
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0
    have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (m + 1) => ρ)
        (ρ.prod (Measure.pi fun _ : Fin m => ρ)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ρ) 0
    set ψ : Fin m → X → ℝ := fun j => φ j.succ
    have ihψ := ih ψ (fun j => hm _) (fun j => hi _) (fun j => h0 _)
    set a : X → ℝ := φ 0
    set b : (Fin m → X) → ℝ := fun z => ∑ j, ψ j (z j)
    set g : X × (Fin m → X) → ℝ := fun p => (a p.1 + b p.2) ^ k
    have hfg : (fun y : Fin (m + 1) → X => (∑ j, φ j (y j)) ^ k) = g ∘ e := by
      funext y
      simp [g, a, b, ψ, e, Fin.sum_univ_succ, Fin.insertNthEquiv, Fin.tail]
    -- the binomial expansion on the product
    have hexp : ∀ p : X × (Fin m → X), g p = ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (a p.1 ^ i * b p.2 ^ (k - i)) := fun p => by
      simp only [g]; rw [add_pow]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hiT : ∀ i ∈ Finset.range (k + 1), Integrable (fun p : X × (Fin m → X) =>
        (k.choose i : ℝ) * (a p.1 ^ i * b p.2 ^ (k - i))) (ρ.prod (Measure.pi fun _ => ρ)) := by
      intro i hi'
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
      refine Integrable.const_mul ?_ _
      exact (int_pow_of_8 ρ (hm 0) (hi 0) (hik.trans hk)).mul_prod
        (ihψ (k - i) (by omega)).1
    have hgi : Integrable g (ρ.prod (Measure.pi fun _ => ρ)) := by
      have := integrable_finsetSum _ hiT
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      exact (hexp p).symm
    have hval : ∫ p, g p ∂(ρ.prod (Measure.pi fun _ => ρ)) = ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ((∫ x, a x ^ i ∂ρ) * ∫ z, b z ^ (k - i) ∂(Measure.pi fun _ => ρ)) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_finsetSum _ hiT]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_prod_mul (fun x => a x ^ i) (fun z => b z ^ (k - i))]
    refine ⟨?_, ?_⟩
    · rw [hfg]
      exact (hmp.integrable_comp_emb e.measurableEmbedding).mpr hgi
    · rw [hfg]
      show |∫ y, g (e y) ∂(Measure.pi fun _ : Fin (m + 1) => ρ)| ≤ _
      rw [hmp.integral_comp' g, hval]
      -- the moment weights of the new row
      set s : ℕ → ℝ := fun i => ∫ x, |a x| ^ i ∂ρ
      have hs0 : ∀ i, 0 ≤ s i := fun i => integral_nonneg fun x => by positivity
      have hcw : ∀ i ≤ 8, |∫ x, a x ^ i ∂ρ| ≤ cw s i := by
        intro i hi8
        rcases i with _ | _ | i
        · simp [cw]
        · simp [cw, a, h0 0]
        · simp only [cw]
          refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [abs_pow])
      have hSm : Smom ρ φ = Smom ρ ψ + s := by
        funext i; simp [Smom, s, ψ, a, Fin.sum_univ_succ, add_comm]
      rw [hSm]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans ?_ (Ek_step hk (Smom ρ ψ) s (Smom_nonneg ρ ψ) hs0)
      refine Finset.sum_le_sum fun i hi' => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      exact mul_le_mul (hcw i (hik.trans hk)) (ihψ (k - i) (by omega)).2 (abs_nonneg _)
        (cw_nonneg i s hs0)

omit [IsProbabilityMeasure ρ] in
/-- Cauchy–Schwarz for integrals. -/
lemma int_cs2 {F G : X → ℝ} (hF : Integrable (fun x => F x ^ 2) ρ)
    (hG : Integrable (fun x => G x ^ 2) ρ) (hFG : Integrable (fun x => F x * G x) ρ) :
    (∫ x, F x * G x ∂ρ) ^ 2 ≤ (∫ x, F x ^ 2 ∂ρ) * ∫ x, G x ^ 2 ∂ρ := by
  set A := ∫ x, F x ^ 2 ∂ρ
  set B := ∫ x, G x ^ 2 ∂ρ
  set C := ∫ x, F x * G x ∂ρ
  have hq : ∀ t : ℝ, 0 ≤ t ^ 2 * A - 2 * t * C + B := by
    intro t
    have h : 0 ≤ ∫ x, (t * F x - G x) ^ 2 ∂ρ := integral_nonneg fun x => sq_nonneg _
    have e : (fun x => (t * F x - G x) ^ 2) =
        fun x => t ^ 2 * F x ^ 2 - 2 * t * (F x * G x) + G x ^ 2 := by funext x; ring
    have i1 : Integrable (fun x => t ^ 2 * F x ^ 2) ρ := hF.const_mul _
    have i2 : Integrable (fun x => 2 * t * (F x * G x)) ρ := hFG.const_mul _
    have i12 : Integrable (fun x => t ^ 2 * F x ^ 2 - 2 * t * (F x * G x)) ρ := i1.sub i2
    rw [e, integral_add i12 hG, integral_sub i1 i2, integral_const_mul,
      integral_const_mul] at h
    linarith
  have hA : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  rcases hA.eq_or_lt with h | h
  · have hC : C = 0 := by
      by_contra hC
      have := hq ((B + 1) / (2 * C))
      rw [← h] at this
      have e : ((B + 1) / (2 * C)) ^ 2 * 0 - 2 * ((B + 1) / (2 * C)) * C + B = -1 := by
        field_simp; ring
      linarith
    rw [hC, ← h]; simp
  · have := hq (C / A)
    have e : (C / A) ^ 2 * A - 2 * (C / A) * C + B = B - C ^ 2 / A := by field_simp; ring
    rw [e, sub_nonneg, div_le_iff₀ h] at this
    linarith

/-- `S_{a+b}² ≤ S_{2a}·S_{2b}` for `a + b ≤ 8`, `2a, 2b ≤ 8`. -/
lemma Smom_cs {m : ℕ} (φ : Fin m → X → ℝ) (hm : ∀ j, Measurable (φ j))
    (hi : ∀ j, Integrable (fun x => φ j x ^ 8) ρ) {a b : ℕ} (ha : 2 * a ≤ 8) (hb : 2 * b ≤ 8) :
    Smom ρ φ (a + b) ^ 2 ≤ Smom ρ φ (2 * a) * Smom ρ φ (2 * b) := by
  have hrow : ∀ j, ∫ x, |φ j x| ^ (a + b) ∂ρ ≤
      √(∫ x, |φ j x| ^ (2 * a) ∂ρ) * √(∫ x, |φ j x| ^ (2 * b) ∂ρ) := by
    intro j
    have hF := int_abs_pow_of_8 ρ (hm j) (hi j) ha
    have hG := int_abs_pow_of_8 ρ (hm j) (hi j) hb
    have hFG := int_abs_pow_of_8 ρ (hm j) (hi j) (k := a + b) (by omega)
    have e1 : (fun x => (|φ j x| ^ a) ^ 2) = fun x => |φ j x| ^ (2 * a) := by
      funext x; rw [← pow_mul, mul_comm]
    have e2 : (fun x => (|φ j x| ^ b) ^ 2) = fun x => |φ j x| ^ (2 * b) := by
      funext x; rw [← pow_mul, mul_comm]
    have e3 : (fun x => |φ j x| ^ a * |φ j x| ^ b) = fun x => |φ j x| ^ (a + b) := by
      funext x; rw [pow_add]
    have h := int_cs2 ρ (F := fun x => |φ j x| ^ a) (G := fun x => |φ j x| ^ b)
      (by rw [e1]; exact hF) (by rw [e2]; exact hG) (by rw [e3]; exact hFG)
    simp only [e1, e2, e3] at h
    rw [← Real.sqrt_mul (integral_nonneg fun x => by positivity)]
    exact Real.le_sqrt_of_sq_le h
  have h0 : 0 ≤ Smom ρ φ (a + b) := Smom_nonneg ρ φ _
  have h1 : Smom ρ φ (a + b) ≤ √(Smom ρ φ (2 * a)) * √(Smom ρ φ (2 * b)) := by
    refine (Finset.sum_le_sum fun j _ => hrow j).trans ?_
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _ |>.trans (le_of_eq (by
      congr 2 <;> exact Finset.sum_congr rfl fun j _ =>
        Real.sq_sqrt (integral_nonneg fun x => by positivity)))
  calc Smom ρ φ (a + b) ^ 2 ≤ (√(Smom ρ φ (2 * a)) * √(Smom ρ φ (2 * b))) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ = _ := by
        rw [mul_pow, Real.sq_sqrt (Smom_nonneg ρ φ _), Real.sq_sqrt (Smom_nonneg ρ φ _)]

/-- **The eighth moment of a sum of independent centred rows**:
`E(Σ_j φ_j)⁸ ≤ 105S₂⁴ + 490S₂²S₄ + 63S₄² + 56S₂S₆ + S₈`, `S_k = Σ_j E|φ_j|^k`. -/
theorem mom8_pi {m : ℕ} (φ : Fin m → X → ℝ) (hm : ∀ j, Measurable (φ j))
    (hi : ∀ j, Integrable (fun x => φ j x ^ 8) ρ) (h0 : ∀ j, ∫ x, φ j x ∂ρ = 0) :
    Integrable (fun y : Fin m → X => (∑ j, φ j (y j)) ^ 8) (Measure.pi fun _ => ρ) ∧
    ∫ y, (∑ j, φ j (y j)) ^ 8 ∂(Measure.pi fun _ : Fin m => ρ) ≤
      105 * Smom ρ φ 2 ^ 4 + 490 * Smom ρ φ 2 ^ 2 * Smom ρ φ 4 + 63 * Smom ρ φ 4 ^ 2 +
        56 * Smom ρ φ 2 * Smom ρ φ 6 + Smom ρ φ 8 := by
  obtain ⟨hI, hB⟩ := mom_all ρ m φ hm hi h0 8 le_rfl
  refine ⟨hI, (le_abs_self _).trans (hB.trans ?_)⟩
  have h3 := Smom_cs ρ φ hm hi (a := 1) (b := 2) (by norm_num) (by norm_num)
  have h5 := Smom_cs ρ φ hm hi (a := 2) (b := 3) (by norm_num) (by norm_num)
  norm_num at h3 h5
  have p2 := Smom_nonneg ρ φ 2
  have p3 := Smom_nonneg ρ φ 3
  have p4 := Smom_nonneg ρ φ 4
  have p5 := Smom_nonneg ρ φ 5
  have p6 := Smom_nonneg ρ φ 6
  simp only [Ek]
  have k1 : 280 * Smom ρ φ 2 * Smom ρ φ 3 ^ 2 ≤ 280 * Smom ρ φ 2 ^ 2 * Smom ρ φ 4 := by
    have := mul_le_mul_of_nonneg_left h3 p2; nlinarith
  have k2 : 56 * Smom ρ φ 3 * Smom ρ φ 5 ≤ 28 * (Smom ρ φ 4 ^ 2 + Smom ρ φ 2 * Smom ρ φ 6) := by
    have hA : (Smom ρ φ 3 * Smom ρ φ 5) ^ 2 ≤ (Smom ρ φ 2 * Smom ρ φ 4) * (Smom ρ φ 4 * Smom ρ φ 6) := by
      rw [mul_pow]; exact mul_le_mul h3 h5 (sq_nonneg _) (by positivity)
    have hB : (Smom ρ φ 2 * Smom ρ φ 4) * (Smom ρ φ 4 * Smom ρ φ 6) =
        (Smom ρ φ 4) ^ 2 * (Smom ρ φ 2 * Smom ρ φ 6) := by ring
    rw [hB] at hA
    have hC : Smom ρ φ 3 * Smom ρ φ 5 ≤ (Smom ρ φ 4 ^ 2 + Smom ρ φ 2 * Smom ρ φ 6) / 2 := by
      nlinarith [sq_nonneg (Smom ρ φ 4 ^ 2 - Smom ρ φ 2 * Smom ρ φ 6),
        mul_nonneg p3 p5, mul_nonneg p2 p6]
    linarith
  nlinarith [mul_nonneg p2 p4, sq_nonneg (Smom ρ φ 2)]

/-- The `lintegral` form of `mom8_pi`. -/
theorem mom8_pi_lint {m : ℕ} (φ : Fin m → X → ℝ) (hm : ∀ j, Measurable (φ j))
    (hi : ∀ j, Integrable (fun x => φ j x ^ 8) ρ) (h0 : ∀ j, ∫ x, φ j x ∂ρ = 0) :
    ∫⁻ y, ENNReal.ofReal ((∑ j, φ j (y j)) ^ 8) ∂(Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal (105 * Smom ρ φ 2 ^ 4 + 490 * Smom ρ φ 2 ^ 2 * Smom ρ φ 4 +
        63 * Smom ρ φ 4 ^ 2 + 56 * Smom ρ φ 2 * Smom ρ φ 6 + Smom ρ φ 8) := by
  obtain ⟨hI, hB⟩ := mom8_pi ρ φ hm hi h0
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun y => (Even.pow_nonneg ⟨4, rfl⟩ _))]
  exact ENNReal.ofReal_le_ofReal hB

end BstLean.Part184

#print axioms BstLean.Part184.mom8_pi
#print axioms BstLean.Part184.mom8_pi_lint
