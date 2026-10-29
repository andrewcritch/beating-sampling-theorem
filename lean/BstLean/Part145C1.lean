import BstLean.Part133CosB

/-!
# Part 145, helper `C1`: the eighth central moment of `|M w|²`

`|M w|²/(v|w|²)` has the chi-square distribution with `m` degrees of freedom. This file gives the
central moments of the orders `1` to `8` of a sum of `m` independent copies of `g² − 1`
(`g` standard Gaussian), and from them the `L²` norm of the fourth power of the normalized
deviation of `|M w|²`.

* `zC j`: `E (g² − 1)^j` for `j ≤ 8`; `gauss_csq_zC`.
* `pC k j`: the `j`-th moment of a sum of `k` copies; `pC_rec` (the binomial recursion);
  `pi_sum_eight_finset`.
* `lin_sq_eight`: `E(|M w|² − m·v|w|²)⁸ = (1680m⁴ + 76160m³ + 467712m² + 645120m)·(v|w|²)⁸`.
* `qCos n = √(1680 + 76160/n + 467712/n² + 645120/n³)/n²`; `dev_four_L2`: the fourth power of
  the normalized deviation of `|M w|²` has `L²` norm at most `|w|⁸·qCos n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133

/-! ## The numbers -/

/-- `E (g² − 1)^j` for a standard Gaussian `g`, `j ≤ 8`. -/
def zC : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 8
  | 4 => 60
  | 5 => 544
  | 6 => 6040
  | 7 => 79008
  | 8 => 1190672
  | _ => 0

/-- The `j`-th moment of a sum of `k` independent copies of `g² − 1`, `j ≤ 8`. -/
def pC (k : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 2 * k
  | 3 => 8 * k
  | 4 => 48 * k + 12 * k ^ 2
  | 5 => 384 * k + 160 * k ^ 2
  | 6 => 3840 * k + 2080 * k ^ 2 + 120 * k ^ 3
  | 7 => 46080 * k + 29568 * k ^ 2 + 3360 * k ^ 3
  | 8 => 645120 * k + 467712 * k ^ 2 + 76160 * k ^ 3 + 1680 * k ^ 4
  | _ => 0

/-- The binomial recursion of the moments: one more copy. -/
lemma pC_rec (k : ℝ) (j : ℕ) (hj : j ≤ 8) :
    ∑ i ∈ Finset.range (j + 1), zC i * pC k (j - i) * (j.choose i : ℝ) = pC (k + 1) j := by
  interval_cases j <;> simp [Finset.sum_range_succ, zC, pC, Nat.choose] <;> ring

/-! ## Lower powers from a higher power -/

lemma integrable_pow_of_le {Ω : Type*} [MeasurableSpace Ω] {ρ : Measure Ω} [IsFiniteMeasure ρ]
    {g : Ω → ℝ} (hg : AEStronglyMeasurable g ρ) {N : ℕ} (hN : Integrable (fun ω => g ω ^ N) ρ)
    (hNe : Even N) {k : ℕ} (hk : k ≤ N) : Integrable (fun ω => g ω ^ k) ρ := by
  have hb : Integrable (fun ω => 1 + g ω ^ N) ρ := (integrable_const (1 : ℝ)).add hN
  refine Integrable.mono' hb (hg.pow k) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  have h4' : |g ω| ^ N = g ω ^ N := hNe.pow_abs _
  have h2 : 0 ≤ g ω ^ N := hNe.pow_nonneg _
  rcases le_total (|g ω|) 1 with h | h
  · have h1 := pow_le_one₀ (n := k) (abs_nonneg _) h
    linarith
  · have h1 := pow_le_pow_right₀ h hk
    linarith

/-! ## The moments of the orders `≤ 8` of a sum of independent copies -/

section pi8

variable {ι : Type*} [Fintype ι] {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem pi_sum_eight_finset {f : ℝ → ℝ} (hf : Measurable f)
    (h8 : Integrable (fun x => f x ^ 8) μ) (hz : ∀ j, j ≤ 8 → ∫ x, f x ^ j ∂μ = zC j)
    (s : Finset ι) :
    Integrable (fun ω : ι → ℝ => (∑ i ∈ s, f (ω i)) ^ 8) (Measure.pi fun _ : ι => μ) ∧
    ∀ j, j ≤ 8 → ∫ ω : ι → ℝ, (∑ i ∈ s, f (ω i)) ^ j ∂(Measure.pi fun _ : ι => μ) =
      pC (s.card : ℝ) j := by
  classical
  have fk : ∀ k, k ≤ 8 → Integrable (fun x => f x ^ k) μ := fun k hk =>
    integrable_pow_of_le hf.aestronglyMeasurable h8 (by decide) hk
  have hind := iIndepFun_pi (μ := fun _ : ι => μ) (X := fun _ => f) (fun _ => hf.aemeasurable)
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp, fun j hj => ?_⟩
    interval_cases j <;> simp [pC]
  | insert a s ha ih =>
    obtain ⟨iS8, eS⟩ := ih
    have mS : Measurable (fun ω : ι → ℝ => ∑ i ∈ s, f (ω i)) :=
      Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i)
    have hSZ : IndepFun (fun ω : ι → ℝ => ∑ i ∈ s, f (ω i)) (fun ω : ι → ℝ => f (ω a))
        (Measure.pi fun _ : ι => μ) := by
      have := hind.indepFun_finsetSum_of_notMem (fun i => hf.comp (measurable_pi_apply i)) ha
      convert this using 1
      funext ω
      simp
    have Sk : ∀ k, k ≤ 8 → Integrable (fun ω : ι → ℝ => (∑ i ∈ s, f (ω i)) ^ k)
        (Measure.pi fun _ : ι => μ) := fun k hk =>
      integrable_pow_of_le mS.aestronglyMeasurable iS8 (by decide) hk
    have Zk : ∀ k, k ≤ 8 → Integrable (fun ω : ι → ℝ => f (ω a) ^ k)
        (Measure.pi fun _ : ι => μ) := fun k hk =>
      integrable_comp_eval (μ := fun _ : ι => μ) (i := a) (fk k hk)
    have eZ : ∀ k, k ≤ 8 → ∫ ω : ι → ℝ, f (ω a) ^ k ∂(Measure.pi fun _ : ι => μ) =
        ∫ x, f x ^ k ∂μ := fun k hk =>
      integral_comp_eval (μ := fun _ : ι => μ) (i := a) (fk k hk).aestronglyMeasurable
    have ind : ∀ i j : ℕ, IndepFun (fun ω : ι → ℝ => f (ω a) ^ i)
        (fun ω : ι → ℝ => (∑ l ∈ s, f (ω l)) ^ j) (Measure.pi fun _ : ι => μ) := fun i j =>
      hSZ.symm.comp (φ := fun x : ℝ => x ^ i) (ψ := fun x : ℝ => x ^ j)
        (measurable_id.pow_const i) (measurable_id.pow_const j)
    have iT : ∀ i j, i ≤ 8 → j ≤ 8 →
        Integrable (fun ω : ι → ℝ => f (ω a) ^ i * (∑ l ∈ s, f (ω l)) ^ j)
          (Measure.pi fun _ : ι => μ) := fun i j hi hj =>
      (ind i j).integrable_mul (Zk i hi) (Sk j hj)
    have eT : ∀ i j, i ≤ 8 → j ≤ 8 →
        ∫ ω : ι → ℝ, f (ω a) ^ i * (∑ l ∈ s, f (ω l)) ^ j ∂(Measure.pi fun _ : ι => μ) =
          zC i * pC (s.card : ℝ) j := fun i j hi hj => by
      rw [(ind i j).integral_fun_mul_eq_mul_integral (Zk i hi).aestronglyMeasurable
        (Sk j hj).aestronglyMeasurable, eZ i hi, hz i hi, eS j hj]
    have hexp : ∀ j : ℕ, (fun ω : ι → ℝ => (∑ i ∈ insert a s, f (ω i)) ^ j) = fun ω =>
        ∑ i ∈ Finset.range (j + 1),
          f (ω a) ^ i * (∑ l ∈ s, f (ω l)) ^ (j - i) * (j.choose i : ℝ) := by
      intro j
      funext ω
      rw [Finset.sum_insert ha, add_pow]
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hexp 8]
      refine integrable_finsetSum _ fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      exact (iT i (8 - i) (by omega) (by omega)).mul_const _
    · rw [hexp j, integral_finsetSum _ fun i hi => by
        have hi' := Finset.mem_range.mp hi
        exact (iT i (j - i) (by omega) (by omega)).mul_const _]
      rw [Finset.sum_congr rfl fun i hi => by
        have hi' := Finset.mem_range.mp hi
        rw [integral_mul_const, eT i (j - i) (by omega) (by omega)]]
      rw [Finset.card_insert_of_notMem ha]
      push_cast
      exact pC_rec _ j hj

end pi8

/-! ## Gaussian moments of `x² − 1` -/

lemma gaussMom_two_mul (i : ℕ) : gaussMom (2 * i) = ((2 * i - 1).doubleFactorial : ℝ) := by
  simp [gaussMom]

lemma gauss_csq_pow (j : ℕ) :
    Integrable (fun x : ℝ => (x ^ 2 - 1) ^ j) (gaussianReal 0 1) ∧
    ∫ x : ℝ, (x ^ 2 - 1) ^ j ∂gaussianReal 0 1 =
      ∑ i ∈ Finset.range (j + 1), gaussMom (2 * i) * (-1) ^ (j - i) * (j.choose i : ℝ) := by
  have e : (fun x : ℝ => (x ^ 2 - 1) ^ j) = fun x =>
      ∑ i ∈ Finset.range (j + 1), x ^ (2 * i) * (-1) ^ (j - i) * (j.choose i : ℝ) := by
    funext x
    rw [sub_eq_add_neg, add_pow]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_mul]
  have hi : ∀ i : ℕ, Integrable (fun x : ℝ => x ^ (2 * i) * (-1) ^ (j - i) * (j.choose i : ℝ))
      (gaussianReal 0 1) := fun i => ((integrable_pow_gauss (2 * i)).mul_const _).mul_const _
  rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => hi i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hi i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_const, integral_mul_const, gaussMom_eq]

lemma gauss_csq_zC (j : ℕ) (hj : j ≤ 8) :
    ∫ x : ℝ, (x ^ 2 - 1) ^ j ∂gaussianReal 0 1 = zC j := by
  rw [(gauss_csq_pow j).2]
  interval_cases j <;>
    norm_num [Finset.sum_range_succ, gaussMom_two_mul, Nat.doubleFactorial, Nat.choose, zC]

/-! ## The eighth central moment of `|M w|²` -/

/-- `E(|M w|² − m·v|w|²)⁸ = (1680m⁴ + 76160m³ + 467712m² + 645120m)·(v|w|²)⁸`. -/
theorem lin_sq_eight {m k : ℕ} {v : ℝ} (hv : 0 ≤ v) (w : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (M.mulVec w) - (m : ℝ) * (v * normSq w)) ^ 8) (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ, (normSq (M.mulVec w) - (m : ℝ) * (v * normSq w)) ^ 8
      ∂gaussMat m k v =
      (1680 * (m : ℝ) ^ 4 + 76160 * (m : ℝ) ^ 3 + 467712 * (m : ℝ) ^ 2 + 645120 * m) *
        (v * normSq w) ^ 8 := by
  classical
  have hg : Measurable (fun y : Fin m → ℝ => (normSq y - (m : ℝ) * (v * normSq w)) ^ 8) :=
    (measurable_normSq.sub measurable_const).pow_const 8
  have e : ∀ ξ : Fin m → ℝ,
      (normSq ((Real.sqrt v * Real.sqrt (normSq w)) • ξ) - (m : ℝ) * (v * normSq w)) ^ 8 =
      (v * normSq w) ^ 8 * (∑ i, (ξ i ^ 2 - 1)) ^ 8 := by
    intro ξ
    rw [normSq_smul, sq_scale hv, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    unfold normSq
    ring
  have hf : Measurable (fun x : ℝ => x ^ 2 - 1) := by fun_prop
  obtain ⟨pi8, pe⟩ := pi_sum_eight_finset (ι := Fin m) (μ := gaussianReal 0 1) hf
    (gauss_csq_pow 8).1 gauss_csq_zC Finset.univ
  have pe8 := pe 8 le_rfl
  refine ⟨layer_transfer_integrable v w hg ?_, ?_⟩
  · simp_rw [e]
    exact pi8.const_mul _
  · rw [layer_transfer v w hg]
    simp_rw [e]
    rw [integral_const_mul]
    unfold stdGauss
    rw [pe8, Finset.card_univ, Fintype.card_fin]
    simp only [pC]
    ring

/-- The bound of the `L²` norm of the fourth power of the normalized deviation of `|M w|²`,
unit `w`: `√(1680 + 76160/n + 467712/n² + 645120/n³)/n²`. -/
noncomputable def qCos (n : ℕ) : ℝ :=
  √(1680 + 76160 / (n : ℝ) + 467712 / (n : ℝ) ^ 2 + 645120 / (n : ℝ) ^ 3) / (n : ℝ) ^ 2

lemma qCos_nonneg (n : ℕ) : 0 ≤ qCos n := by unfold qCos; positivity

/-- The fourth power of the normalized deviation of `|M w|²` has `L²` norm at most
`|w|⁸·qCos n`. -/
lemma dev_four_L2 {n k : ℕ} {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) (w : Fin k → ℝ) :
    L2le (gaussMat n k v)
      (fun M : Matrix (Fin n) (Fin k) ℝ =>
        ((normSq (M.mulVec w) - (n : ℝ) * (v * normSq w)) / ((n : ℝ) * v)) ^ 4)
      (normSq w ^ 4 * qCos n) := by
  obtain ⟨hi, he⟩ := lin_sq_eight (m := n) hv.le w
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ∀ M : Matrix (Fin n) (Fin k) ℝ,
      (((normSq (M.mulVec w) - (n : ℝ) * (v * normSq w)) / ((n : ℝ) * v)) ^ 4) ^ 2 =
        (normSq (M.mulVec w) - (n : ℝ) * (v * normSq w)) ^ 8 / ((n : ℝ) * v) ^ 8 := fun M => by
    ring
  refine L2le.mk' ?_ ?_ ?_
  · exact ((((measurable_normSq_mulVec w).sub_const _).div_const _).pow_const
      4).aestronglyMeasurable
  · simp only [e]
    exact hi.div_const _
  · simp only [e]
    have hsq : (√(1680 + 76160 / (n : ℝ) + 467712 / (n : ℝ) ^ 2 + 645120 / (n : ℝ) ^ 3)) ^ 2 =
        1680 + 76160 / (n : ℝ) + 467712 / (n : ℝ) ^ 2 + 645120 / (n : ℝ) ^ 3 :=
      Real.sq_sqrt (by positivity)
    have e2 : (normSq w ^ 4 * qCos n) ^ 2 = normSq w ^ 8 *
        ((1680 + 76160 / (n : ℝ) + 467712 / (n : ℝ) ^ 2 + 645120 / (n : ℝ) ^ 3) /
          (n : ℝ) ^ 4) := by
      unfold qCos
      rw [mul_pow, div_pow, hsq]; ring
    rw [integral_div, he, e2]
    apply le_of_eq
    field_simp

end BstLean.Part145

open BstLean.Part145 in
#print axioms lin_sq_eight
open BstLean.Part145 in
#print axioms dev_four_L2
