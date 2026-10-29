import BstLean.Part59Defs

/-!
# Part 59, wave 2: the assembly at one law, and the translation between the coefficient form and the
tensor form

Specification: `delegations/answers/p59-spec-opus.md` §4.

* `fail_subset59`, `fail59`: copies of Part 53's `fail_subset53`, `fail53` for laws with `dD/dσ ≤ K`
  (`UpLaw`): from Props T1* and T2* (as hypotheses) the failure probability is `≤ δ` for `n ≥ n₀`.
* `BP_eq59`, `varP_eq59`: under `CoefTens59`, `B` and `Var` of `polyEval k c` are Part 43's `BofQ` and
  `varFQ` of the tensor form.
* `cost_lt_baselineF59`: a cost `≤ costG59 < baselineF` is below the baseline.

Proved here, with no `sorry`. This file imports `Part59Defs` only. Do not use `native_decide` or
`axiom` anywhere.
-/

namespace BstLean.Part59

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD mapMD)
open BstLean.Part41 (Mono frob Tens TSymm varU)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (g0 Ncirc)

variable {n d : ℕ}

/-- The union-bound inclusion of Theorem DL1's proof. -/
theorem fail_subset59 (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n) (ε s : ℝ) :
    {Z : CoefIdxD n d → ℝ | Z ≠ 0 ∧
        ε ^ 2 * varFQ μ k f0 T (unitOfD Z) < (BofQ μ k f0 T (unitOfD Z) - g0 n d k f0 T (unitOfD Z)) ^ 2} ⊆
      {Z | Z ≠ 0 ∧ varFQ μ k f0 T (unitOfD Z) < s * Ncirc n d k f0 T} ∪
      {Z | Z ≠ 0 ∧ ε ^ 2 * s * Ncirc n d k f0 T ≤
        (BofQ μ k f0 T (unitOfD Z) - g0 n d k f0 T (unitOfD Z)) ^ 2} := by
  intro Z ⟨hZ, hf⟩
  by_cases hV : varFQ μ k f0 T (unitOfD Z) < s * Ncirc n d k f0 T
  · exact Or.inl ⟨hZ, hV⟩
  · refine Or.inr ⟨hZ, ?_⟩
    push Not at hV
    have : ε ^ 2 * (s * Ncirc n d k f0 T) ≤ ε ^ 2 * varFQ μ k f0 T (unitOfD Z) :=
      mul_le_mul_of_nonneg_left hV (sq_nonneg ε)
    nlinarith

/-- **The failure bound** from Props T1 and T2. -/
theorem fail59 (d k : ℕ) (K ε δ p s C1 C2 : ℝ) (n1 n2 : ℕ) (hε : 0 < ε) (hs : 0 < s) (hp0 : 0 ≤ p) (hp : p < δ)
    (h1 : PropT1_59 d k K C1 n1) (h2 : PropT2_59 d k K p s C2 n2) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ μ k f0 T (unitOfD Z) <
            (BofQ μ k f0 T (unitOfD Z) - g0 n d k f0 T (unitOfD Z)) ^ 2} ≤ ENNReal.ofReal δ := by
  set A : ℝ := |C2| / s + |C1| / (ε ^ 2 * s) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max (max n1 n2) (⌈A / (δ - p)⌉₊ + 1), fun n hn μ hμ f0 T hT hTk => ?_⟩
  have hn1 : n1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : n2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : ⌈A / (δ - p)⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by
    have : (1 : ℕ) ≤ n := le_trans (by omega) hn3
    exact_mod_cast this
  have hc : 0 < ε ^ 2 * s := by positivity
  have hb1 := h1 n hn1 μ hμ f0 T hT hTk (ε ^ 2 * s) hc
  have hb2 := h2 n hn2 μ hμ f0 T hT hTk
  refine le_trans (measure_mono (fail_subset59 (d := d) μ k f0 T ε s)) ?_
  refine le_trans (measure_union_le _ _) ?_
  refine le_trans (add_le_add hb2 hb1) ?_
  have hδp : 0 < δ - p := by linarith
  have hnA : A / (δ - p) < n := by
    have h := Nat.le_ceil (A / (δ - p))
    have : ((⌈A / (δ - p)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn3
    push_cast at this
    linarith
  have hAn : A / n ≤ δ - p := by
    rw [div_le_iff₀ hnpos]
    rw [div_lt_iff₀ hδp] at hnA
    linarith
  have e1 : C2 / (n * s) ≤ |C2| / s / n := by
    rw [div_div, mul_comm s]
    exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
  have e2 : C1 / (n * (ε ^ 2 * s)) ≤ |C1| / (ε ^ 2 * s) / n := by
    rw [div_div, mul_comm (ε ^ 2 * s)]
    exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
  have hAn' : A / n = |C2| / s / n + |C1| / (ε ^ 2 * s) / n := by rw [hA, add_div]
  have hsum : p + C2 / (n * s) + C1 / (n * (ε ^ 2 * s)) ≤ δ := by linarith
  calc ENNReal.ofReal (p + C2 / (n * s)) + ENNReal.ofReal (C1 / (n * (ε ^ 2 * s)))
      ≤ ENNReal.ofReal (max (p + C2 / (n * s)) 0 + max (C1 / (n * (ε ^ 2 * s))) 0) := by
        rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
        gcongr <;> exact le_max_left _ _
    _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal
        have hC1' : 0 ≤ |C1| / (ε ^ 2 * s) / n := by positivity
        have hC2' : 0 ≤ |C2| / s / n := by positivity
        have : max (p + C2 / (n * s)) 0 ≤ p + |C2| / s / n :=
          max_le (by linarith) (by linarith)
        have : max (C1 / (n * (ε ^ 2 * s))) 0 ≤ |C1| / (ε ^ 2 * s) / n :=
          max_le e2 hC1'
        linarith

/-- `B` of the coefficient form is `BofQ` of the tensor form. -/
theorem BP_eq59 (hCT : CoefTens59) (μ : Measure (Fin n → ℝ)) (k : ℕ) (c : Mono n k → ℝ)
    (M : CoefIdxD n d → ℝ) : BP μ k c M = BofQ μ k (c default) (tensOf k c) M := by
  unfold BP BofQ
  congr 1
  funext x
  rw [(hCT n k c).2.1]

/-- `Var` of the coefficient form is `varFQ` of the tensor form. -/
theorem varP_eq59 (hCT : CoefTens59) (μ : Measure (Fin n → ℝ)) (k : ℕ) (c : Mono n k → ℝ)
    (M : CoefIdxD n d → ℝ) : varP μ k c M = varFQ μ k (c default) (tensOf k c) M := by
  unfold varP varFQ
  have h : (fun x => polyEval k c (mapMD M x)) =
      fun x => BstLean.Part41.fval k (c default) (tensOf k c) (mapMD M x) := by
    funext x; rw [(hCT n k c).2.1]
  rw [h]

/-- The program's input vector gives back `c` and `M`. -/
theorem cv59_inp (k : ℕ) (c : Mono n k → ℝ) (M : CoefIdxD n d → ℝ) :
    cv59 (inp59 c M) = c ∧ Mv59 (inp59 c M) = M := ⟨rfl, rfl⟩

/-- A cost `≤ costG59 < baselineF` is below the baseline. -/
theorem cost_lt_baselineF59 (k : ℕ) (ε : ℝ) (c : ℕ) (hc : (c : ℝ) ≤ costG59 n d k)
    (hlt : costG59 n d k < baselineF n d k ε) : (c : ℝ) < baselineF n d k ε :=
  lt_of_le_of_lt hc hlt

end BstLean.Part59
