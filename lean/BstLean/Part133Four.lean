import BstLean.Part133L2

/-!
# Part 133: fourth moments of one Gaussian matrix

Role: `delegations/statements/p133-spec.md`.

* `pi_sum_four_finset`: for independent copies of a centred `f`:
  `E (Σ_{i ∈ s} f(ω_i))⁴ = |s|·E f⁴ + 3|s|(|s| − 1)·(E f²)²`.
* `lin_sq_four`: `E(|M w|² − m·v|w|²)⁴ = (12m² + 48m)·(v|w|²)⁴`.
* `lin_dot_var`: `E(⟨Mh, Mh′⟩ − m·v⟨h, h′⟩)² = m·v²·(|h|²|h′|² + ⟨h, h′⟩²)`.
* `lin_ctp_var`: unit `h, h′`, `τ = ⟨h, h′⟩`:
  `E(⟨Mh, Mh′⟩ − τ(|Mh|² + |Mh′|²)/2)² = m·v²·(1 − τ²)²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part133

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part130 BstLean.Part131 BstLean.Part132

/-! ## Lower powers from the fourth power -/

lemma integrable_pow_of_four {Ω : Type*} [MeasurableSpace Ω] {ρ : Measure Ω} [IsFiniteMeasure ρ]
    {g : Ω → ℝ} (hg : AEStronglyMeasurable g ρ) (h4 : Integrable (fun ω => g ω ^ 4) ρ) {k : ℕ}
    (hk : k ≤ 4) : Integrable (fun ω => g ω ^ k) ρ := by
  have hb : Integrable (fun ω => 1 + g ω ^ 4) ρ := (integrable_const (1 : ℝ)).add h4
  refine Integrable.mono' hb (hg.pow k) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  have h4' : |g ω| ^ 4 = g ω ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  rcases le_total (|g ω|) 1 with h | h
  · have h1 := pow_le_one₀ (n := k) (abs_nonneg _) h
    have h2 : 0 ≤ g ω ^ 4 := by positivity
    linarith
  · have h1 := pow_le_pow_right₀ h hk
    linarith

/-! ## The fourth moment of a sum of independent centred copies -/

section pi4

variable {ι : Type*} [Fintype ι] {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem pi_sum_four_finset {f : ℝ → ℝ} (hf : Measurable f)
    (h4 : Integrable (fun x => f x ^ 4) μ) (h0 : ∫ x, f x ∂μ = 0) (s : Finset ι) :
    Integrable (fun ω : ι → ℝ => (∑ i ∈ s, f (ω i)) ^ 4) (Measure.pi fun _ : ι => μ) ∧
    ∫ ω : ι → ℝ, (∑ i ∈ s, f (ω i)) ∂(Measure.pi fun _ : ι => μ) = 0 ∧
    ∫ ω : ι → ℝ, (∑ i ∈ s, f (ω i)) ^ 2 ∂(Measure.pi fun _ : ι => μ) =
      s.card * ∫ x, f x ^ 2 ∂μ ∧
    ∫ ω : ι → ℝ, (∑ i ∈ s, f (ω i)) ^ 4 ∂(Measure.pi fun _ : ι => μ) =
      s.card * ∫ x, f x ^ 4 ∂μ +
        3 * s.card * ((s.card : ℝ) - 1) * (∫ x, f x ^ 2 ∂μ) ^ 2 := by
  classical
  have fk : ∀ k, k ≤ 4 → Integrable (fun x => f x ^ k) μ := fun k hk =>
    integrable_pow_of_four hf.aestronglyMeasurable h4 hk
  have hind := iIndepFun_pi (μ := fun _ : ι => μ) (X := fun _ => f) (fun _ => hf.aemeasurable)
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨iS4, eS1, eS2, eS4⟩ := ih
    have mS : Measurable (fun ω : ι → ℝ => ∑ i ∈ s, f (ω i)) :=
      Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i)
    have hSZ : IndepFun (fun ω : ι → ℝ => ∑ i ∈ s, f (ω i)) (fun ω : ι → ℝ => f (ω a))
        (Measure.pi fun _ : ι => μ) := by
      have := hind.indepFun_finsetSum_of_notMem (fun i => hf.comp (measurable_pi_apply i)) ha
      convert this using 1
      funext ω
      simp
    have Sk : ∀ k, k ≤ 4 → Integrable (fun ω : ι → ℝ => (∑ i ∈ s, f (ω i)) ^ k)
        (Measure.pi fun _ : ι => μ) := fun k hk =>
      integrable_pow_of_four mS.aestronglyMeasurable iS4 hk
    have Zk : ∀ k, k ≤ 4 → Integrable (fun ω : ι → ℝ => f (ω a) ^ k)
        (Measure.pi fun _ : ι => μ) := fun k hk =>
      integrable_comp_eval (μ := fun _ : ι => μ) (i := a) (fk k hk)
    have eZ : ∀ k, k ≤ 4 → ∫ ω : ι → ℝ, f (ω a) ^ k ∂(Measure.pi fun _ : ι => μ) =
        ∫ x, f x ^ k ∂μ := fun k hk =>
      integral_comp_eval (μ := fun _ : ι => μ) (i := a) (fk k hk).aestronglyMeasurable
    have ind : ∀ i j : ℕ, IndepFun (fun ω : ι → ℝ => (∑ i ∈ s, f (ω i)) ^ i)
        (fun ω : ι → ℝ => f (ω a) ^ j) (Measure.pi fun _ : ι => μ) := fun i j =>
      hSZ.comp (φ := fun x : ℝ => x ^ i) (ψ := fun x : ℝ => x ^ j)
        (measurable_id.pow_const i) (measurable_id.pow_const j)
    have iT : ∀ i j, i ≤ 4 → j ≤ 4 →
        Integrable (fun ω : ι → ℝ => (∑ i ∈ s, f (ω i)) ^ i * f (ω a) ^ j)
          (Measure.pi fun _ : ι => μ) := fun i j hi hj =>
      (ind i j).integrable_mul (Sk i hi) (Zk j hj)
    have eT : ∀ i j, i ≤ 4 → j ≤ 4 →
        ∫ ω : ι → ℝ, (∑ i ∈ s, f (ω i)) ^ i * f (ω a) ^ j ∂(Measure.pi fun _ : ι => μ) =
          (∫ ω : ι → ℝ, (∑ i ∈ s, f (ω i)) ^ i ∂(Measure.pi fun _ : ι => μ)) *
            ∫ x, f x ^ j ∂μ := fun i j hi hj => by
      rw [(ind i j).integral_fun_mul_eq_mul_integral (Sk i hi).aestronglyMeasurable
        (Zk j hj).aestronglyMeasurable, eZ j hj]
    have hins : ∀ ω : ι → ℝ, ∑ i ∈ insert a s, f (ω i) = f (ω a) + ∑ i ∈ s, f (ω i) :=
      fun ω => Finset.sum_insert ha
    have s0 : ∫ ω : ι → ℝ, (∑ i ∈ s, f (ω i)) ^ 0 ∂(Measure.pi fun _ : ι => μ) = 1 := by simp
    have s1 : ∫ ω : ι → ℝ, (∑ i ∈ s, f (ω i)) ^ 1 ∂(Measure.pi fun _ : ι => μ) = 0 := by
      simpa using eS1
    have f0 : ∫ x, f x ^ 0 ∂μ = 1 := by simp
    have f1 : ∫ x, f x ^ 1 ∂μ = 0 := by simpa using h0
    simp only [hins, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
    have j04 := iT 0 4 (by norm_num) le_rfl
    have j13 := iT 1 3 (by norm_num) (by norm_num)
    have j22 := iT 2 2 (by norm_num) (by norm_num)
    have j31 := iT 3 1 (by norm_num) (by norm_num)
    have j40 := iT 4 0 le_rfl (by norm_num)
    have j01 := iT 0 1 (by norm_num) (by norm_num)
    have j10 := iT 1 0 (by norm_num) (by norm_num)
    have j02 := iT 0 2 (by norm_num) (by norm_num)
    have j11 := iT 1 1 (by norm_num) (by norm_num)
    have j20 := iT 2 0 (by norm_num) (by norm_num)
    -- fourth power
    have e4 : (fun ω : ι → ℝ => (f (ω a) + ∑ i ∈ s, f (ω i)) ^ 4) = fun ω =>
        (∑ i ∈ s, f (ω i)) ^ 0 * f (ω a) ^ 4 + 4 * ((∑ i ∈ s, f (ω i)) ^ 1 * f (ω a) ^ 3) +
          6 * ((∑ i ∈ s, f (ω i)) ^ 2 * f (ω a) ^ 2) +
          4 * ((∑ i ∈ s, f (ω i)) ^ 3 * f (ω a) ^ 1) + (∑ i ∈ s, f (ω i)) ^ 4 * f (ω a) ^ 0 := by
      funext ω; ring
    have A1 : Integrable (fun ω : ι → ℝ => (∑ i ∈ s, f (ω i)) ^ 0 * f (ω a) ^ 4 +
        4 * ((∑ i ∈ s, f (ω i)) ^ 1 * f (ω a) ^ 3)) (Measure.pi fun _ : ι => μ) :=
      j04.add (j13.const_mul 4)
    have A2 : Integrable (fun ω : ι → ℝ => (∑ i ∈ s, f (ω i)) ^ 0 * f (ω a) ^ 4 +
        4 * ((∑ i ∈ s, f (ω i)) ^ 1 * f (ω a) ^ 3) +
        6 * ((∑ i ∈ s, f (ω i)) ^ 2 * f (ω a) ^ 2)) (Measure.pi fun _ : ι => μ) :=
      A1.add (j22.const_mul 6)
    have A3 : Integrable (fun ω : ι → ℝ => (∑ i ∈ s, f (ω i)) ^ 0 * f (ω a) ^ 4 +
        4 * ((∑ i ∈ s, f (ω i)) ^ 1 * f (ω a) ^ 3) +
        6 * ((∑ i ∈ s, f (ω i)) ^ 2 * f (ω a) ^ 2) +
        4 * ((∑ i ∈ s, f (ω i)) ^ 3 * f (ω a) ^ 1)) (Measure.pi fun _ : ι => μ) :=
      A2.add (j31.const_mul 4)
    -- second power
    have e2 : (fun ω : ι → ℝ => (f (ω a) + ∑ i ∈ s, f (ω i)) ^ 2) = fun ω =>
        (∑ i ∈ s, f (ω i)) ^ 0 * f (ω a) ^ 2 + 2 * ((∑ i ∈ s, f (ω i)) ^ 1 * f (ω a) ^ 1) +
          (∑ i ∈ s, f (ω i)) ^ 2 * f (ω a) ^ 0 := by
      funext ω; ring
    have B1 : Integrable (fun ω : ι → ℝ => (∑ i ∈ s, f (ω i)) ^ 0 * f (ω a) ^ 2 +
        2 * ((∑ i ∈ s, f (ω i)) ^ 1 * f (ω a) ^ 1)) (Measure.pi fun _ : ι => μ) :=
      j02.add (j11.const_mul 2)
    -- first power
    have e1 : (fun ω : ι → ℝ => f (ω a) + ∑ i ∈ s, f (ω i)) = fun ω =>
        (∑ i ∈ s, f (ω i)) ^ 0 * f (ω a) ^ 1 + (∑ i ∈ s, f (ω i)) ^ 1 * f (ω a) ^ 0 := by
      funext ω; ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e4]
      exact A3.add j40
    · rw [e1, integral_add j01 j10, eT 0 1 (by norm_num) (by norm_num),
        eT 1 0 (by norm_num) (by norm_num), s0, s1, f0, f1]
      ring
    · rw [e2, integral_add B1 j20, integral_add j02 (j11.const_mul 2), integral_const_mul,
        eT 0 2 (by norm_num) (by norm_num), eT 1 1 (by norm_num) (by norm_num),
        eT 2 0 (by norm_num) (by norm_num), s0, s1, f0, f1, eS2]
      ring
    · rw [e4, integral_add A3 j40, integral_add A2 (j31.const_mul 4),
        integral_add A1 (j22.const_mul 6), integral_add j04 (j13.const_mul 4),
        integral_const_mul, integral_const_mul, integral_const_mul,
        eT 0 4 (by norm_num) le_rfl, eT 1 3 (by norm_num) (by norm_num),
        eT 2 2 (by norm_num) (by norm_num), eT 3 1 (by norm_num) (by norm_num),
        eT 4 0 le_rfl (by norm_num), s0, s1, f0, f1, eS2, eS4]
      ring

end pi4

/-! ## Gaussian moments of `x² − 1` -/

lemma gaussMom_vals : gaussMom 2 = 1 ∧ gaussMom 4 = 3 ∧ gaussMom 6 = 15 ∧ gaussMom 8 = 105 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    unfold gaussMom
    split_ifs with h
    · norm_num [Nat.doubleFactorial]
    · exact absurd (by decide) h

lemma gauss_csq_moments :
    ∫ x : ℝ, (x ^ 2 - 1) ∂gaussianReal 0 1 = 0 ∧
    ∫ x : ℝ, (x ^ 2 - 1) ^ 2 ∂gaussianReal 0 1 = 2 ∧
    Integrable (fun x : ℝ => (x ^ 2 - 1) ^ 4) (gaussianReal 0 1) ∧
    ∫ x : ℝ, (x ^ 2 - 1) ^ 4 ∂gaussianReal 0 1 = 60 := by
  obtain ⟨g2, g4, g6, g8⟩ := gaussMom_vals
  have p := integrable_pow_gauss
  obtain ⟨-, e1⟩ := integral_lin4 (μ := gaussianReal 0 1) (p 2) (p 2) (p 2) (p 2) (-1) 1 0 0 0
  obtain ⟨-, e2⟩ := integral_lin4 (μ := gaussianReal 0 1) (p 4) (p 2) (p 2) (p 2) 1 1 2 0 0
  obtain ⟨i4, e4⟩ := integral_lin4 (μ := gaussianReal 0 1) (p 8) (p 6) (p 4) (p 2) 1 1 4 (-6) 4
  have f1 : (fun x : ℝ => x ^ 2 - 1) =
      fun x => 1 * x ^ 2 + -1 - 0 * x ^ 2 - 0 * x ^ 2 - 0 * x ^ 2 := by funext x; ring
  have f2 : (fun x : ℝ => (x ^ 2 - 1) ^ 2) =
      fun x => 1 * x ^ 4 + 1 - 2 * x ^ 2 - 0 * x ^ 2 - 0 * x ^ 2 := by funext x; ring
  have f4 : (fun x : ℝ => (x ^ 2 - 1) ^ 4) =
      fun x => 1 * x ^ 8 + 1 - 4 * x ^ 6 - -6 * x ^ 4 - 4 * x ^ 2 := by funext x; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [f1, e1, gaussMom_eq, g2]; ring
  · rw [f2, e2, gaussMom_eq, gaussMom_eq, g2, g4]; ring
  · rw [f4]; exact i4
  · rw [f4, e4, gaussMom_eq, gaussMom_eq, gaussMom_eq, gaussMom_eq, g2, g4, g6, g8]; ring

/-! ## The fourth central moment of `|M w|²` -/

variable {m k : ℕ}

/-- `E(|M w|² − m·v|w|²)⁴ = (12m² + 48m)·(v|w|²)⁴`. -/
theorem lin_sq_four {m k : ℕ} {v : ℝ} (hv : 0 ≤ v) (w : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (M.mulVec w) - (m : ℝ) * (v * normSq w)) ^ 4) (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ, (normSq (M.mulVec w) - (m : ℝ) * (v * normSq w)) ^ 4
      ∂gaussMat m k v = (12 * (m : ℝ) ^ 2 + 48 * m) * (v * normSq w) ^ 4 := by
  classical
  obtain ⟨c1, c2, ci4, c4⟩ := gauss_csq_moments
  have hg : Measurable (fun y : Fin m → ℝ => (normSq y - (m : ℝ) * (v * normSq w)) ^ 4) :=
    (measurable_normSq.sub measurable_const).pow_const 4
  have e : ∀ ξ : Fin m → ℝ,
      (normSq ((Real.sqrt v * Real.sqrt (normSq w)) • ξ) - (m : ℝ) * (v * normSq w)) ^ 4 =
      (v * normSq w) ^ 4 * (∑ i, (ξ i ^ 2 - 1)) ^ 4 := by
    intro ξ
    rw [normSq_smul, sq_scale hv, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    unfold normSq
    ring
  have hf : Measurable (fun x : ℝ => x ^ 2 - 1) := by fun_prop
  obtain ⟨pi4, -, -, pe4⟩ := pi_sum_four_finset (ι := Fin m) (μ := gaussianReal 0 1) hf ci4 c1
    Finset.univ
  refine ⟨layer_transfer_integrable v w hg ?_, ?_⟩
  · simp_rw [e]
    exact pi4.const_mul _
  · rw [layer_transfer v w hg]
    simp_rw [e]
    rw [integral_const_mul]
    unfold stdGauss
    rw [pe4, c2, c4, Finset.card_univ, Fintype.card_fin]
    ring

/-! ## One Gaussian row: linear forms -/

lemma dotp_add_right {ι : Type*} [Fintype ι] (x a b : ι → ℝ) :
    dotp x (a + b) = dotp x a + dotp x b := by
  simp only [dotp, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dotp_sub_right {ι : Type*} [Fintype ι] (x a b : ι → ℝ) :
    dotp x (a - b) = dotp x a - dotp x b := by
  simp only [dotp, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma normSq_add {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    normSq (a + b) = normSq a + normSq b + 2 * dotp a b := by
  simp only [normSq, dotp, Pi.add_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma normSq_sub {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    normSq (a - b) = normSq a + normSq b - 2 * dotp a b := by
  simp only [normSq, dotp, Pi.sub_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma mulVec_eq_dotp_row (M : Matrix (Fin m) (Fin k) ℝ) (w : Fin k → ℝ) (i : Fin m) :
    (M.mulVec w) i = dotp (rowOf i M) w := rfl

lemma measurable_dotp_left (w : Fin k → ℝ) : Measurable (fun r : Fin k → ℝ => dotp r w) :=
  measurable_dotp_comp measurable_id measurable_const

/-- The second moment of a linear form of one Gaussian row. -/
lemma row_two {v : ℝ} (hv : 0 ≤ v) (w : Fin k → ℝ) :
    Integrable (fun ξ : Fin k → ℝ => dotp (Real.sqrt v • ξ) w ^ 2) (stdGauss (Fin k)) ∧
    ∫ ξ : Fin k → ℝ, dotp (Real.sqrt v • ξ) w ^ 2 ∂stdGauss (Fin k) = v * normSq w := by
  obtain ⟨i2, e2⟩ := layer_lin_sq (m := 1) hv w
  have hg : Measurable (fun r : Fin k → ℝ => dotp r w ^ 2) :=
    (measurable_dotp_left w).pow_const 2
  have e : ∀ M : Matrix (Fin 1) (Fin k) ℝ, normSq (M.mulVec w) = dotp (rowOf 0 M) w ^ 2 := by
    intro M
    simp [normSq, mulVec_eq_dotp_row]
  simp_rw [e] at i2 e2
  refine ⟨(row_integrable_iff v 0 hg).1 i2, ?_⟩
  rw [← row_integral v (0 : Fin 1) hg, e2]
  simp

/-- The fourth moment of a linear form of one Gaussian row. -/
lemma row_four {v : ℝ} (hv : 0 ≤ v) (w : Fin k → ℝ) :
    Integrable (fun ξ : Fin k → ℝ => dotp (Real.sqrt v • ξ) w ^ 4) (stdGauss (Fin k)) ∧
    ∫ ξ : Fin k → ℝ, dotp (Real.sqrt v • ξ) w ^ 4 ∂stdGauss (Fin k) = 3 * (v * normSq w) ^ 2 := by
  obtain ⟨i4, e4⟩ := layer_lin_four (m := 1) hv w
  have hg : Measurable (fun r : Fin k → ℝ => dotp r w ^ 4) :=
    (measurable_dotp_left w).pow_const 4
  have e : ∀ M : Matrix (Fin 1) (Fin k) ℝ, normSq (M.mulVec w) ^ 2 = dotp (rowOf 0 M) w ^ 4 := by
    intro M
    simp [normSq, mulVec_eq_dotp_row]
    ring
  simp_rw [e] at i4 e4
  refine ⟨(row_integrable_iff v 0 hg).1 i4, ?_⟩
  rw [← row_integral v (0 : Fin 1) hg, e4]
  norm_num

/-! ## The variance of `⟨Mh, Mh′⟩` -/

/-- `E(⟨Mh, Mh′⟩ − m·v⟨h, h′⟩)² = m·v²·(|h|²|h′|² + ⟨h, h′⟩²)`. -/
theorem lin_dot_var {m k : ℕ} {v : ℝ} (hv : 0 ≤ v) (h h' : Fin k → ℝ) :
    ∫ M : Matrix (Fin m) (Fin k) ℝ, (dotp (M.mulVec h) (M.mulVec h') - (m : ℝ) * (v * dotp h h')) ^ 2
      ∂gaussMat m k v = (m : ℝ) * v ^ 2 * (normSq h * normSq h' + dotp h h' ^ 2) := by
  obtain ⟨iP2, eP2⟩ := row_two hv (h + h')
  obtain ⟨iQ2, eQ2⟩ := row_two hv (h - h')
  obtain ⟨iP4, eP4⟩ := row_four hv (h + h')
  obtain ⟨iQ4, eQ4⟩ := row_four hv (h - h')
  obtain ⟨iU4, eU4⟩ := row_four hv h
  obtain ⟨iV4, eV4⟩ := row_four hv h'
  set f : (Fin k → ℝ) → ℝ := fun r => dotp r h * dotp r h' - v * dotp h h' with hfdef
  have hf : Measurable f :=
    ((measurable_dotp_left h).mul (measurable_dotp_left h')).sub measurable_const
  -- the mean of one row
  have f1 : (fun ξ : Fin k → ℝ => f (Real.sqrt v • ξ)) = fun ξ =>
      1 / 4 * dotp (Real.sqrt v • ξ) (h + h') ^ 2 + -(v * dotp h h') -
        1 / 4 * dotp (Real.sqrt v • ξ) (h - h') ^ 2 - 0 * dotp (Real.sqrt v • ξ) (h - h') ^ 2 -
        0 * dotp (Real.sqrt v • ξ) (h - h') ^ 2 := by
    funext ξ
    simp only [hfdef, dotp_add_right, dotp_sub_right]
    ring
  obtain ⟨-, m1⟩ := integral_lin4 (μ := stdGauss (Fin k)) iP2 iQ2 iQ2 iQ2 (-(v * dotp h h'))
    (1 / 4) (1 / 4) 0 0
  have mean0 : ∫ ξ : Fin k → ℝ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) = 0 := by
    rw [f1, m1, eP2, eQ2, normSq_add, normSq_sub]
    ring
  -- `U²V²`
  have g1 : (fun ξ : Fin k → ℝ =>
      (dotp (Real.sqrt v • ξ) h * dotp (Real.sqrt v • ξ) h') ^ 2) = fun ξ =>
      1 / 12 * dotp (Real.sqrt v • ξ) (h + h') ^ 4 + 0 -
        -(1 / 12) * dotp (Real.sqrt v • ξ) (h - h') ^ 4 - 1 / 6 * dotp (Real.sqrt v • ξ) h ^ 4 -
        1 / 6 * dotp (Real.sqrt v • ξ) h' ^ 4 := by
    funext ξ
    simp only [dotp_add_right, dotp_sub_right]
    ring
  obtain ⟨ig, mg⟩ := integral_lin4 (μ := stdGauss (Fin k)) iP4 iQ4 iU4 iV4 0
    (1 / 12) (-(1 / 12)) (1 / 6) (1 / 6)
  rw [← g1] at ig mg
  -- the second moment of one row
  have f2 : (fun ξ : Fin k → ℝ => f (Real.sqrt v • ξ) ^ 2) = fun ξ =>
      1 * (dotp (Real.sqrt v • ξ) h * dotp (Real.sqrt v • ξ) h') ^ 2 + (v * dotp h h') ^ 2 -
        (v * dotp h h' / 2) * dotp (Real.sqrt v • ξ) (h + h') ^ 2 -
        -(v * dotp h h' / 2) * dotp (Real.sqrt v • ξ) (h - h') ^ 2 -
        0 * dotp (Real.sqrt v • ξ) (h - h') ^ 2 := by
    funext ξ
    simp only [hfdef, dotp_add_right, dotp_sub_right]
    ring
  obtain ⟨i2, m2⟩ := integral_lin4 (μ := stdGauss (Fin k)) ig iP2 iQ2 iQ2 ((v * dotp h h') ^ 2)
    1 (v * dotp h h' / 2) (-(v * dotp h h' / 2)) 0
  rw [← f2] at i2 m2
  obtain ⟨-, es⟩ := rows_sum_sq (m := m) v f hf i2
  have hsum : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (M.mulVec h) (M.mulVec h') - (m : ℝ) * (v * dotp h h') = ∑ i, f (rowOf i M) := by
    intro M
    simp only [hfdef, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rfl
  simp_rw [hsum]
  rw [es, mean0, m2, mg, eP4, eQ4, eU4, eV4, eP2, eQ2, normSq_add, normSq_sub]
  ring

/-- Unit `h, h′`, `τ = ⟨h, h′⟩`: `E(⟨Mh, Mh′⟩ − τ(|Mh|² + |Mh′|²)/2)² = m·v²·(1 − τ²)²`. -/
theorem lin_ctp_var {m k : ℕ} {v : ℝ} (hv : 0 ≤ v) {h h' : Fin k → ℝ} (hh : normSq h = 1)
    (hh' : normSq h' = 1) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => (dotp (M.mulVec h) (M.mulVec h') -
      dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) ^ 2) (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ, (dotp (M.mulVec h) (M.mulVec h') -
      dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) ^ 2 ∂gaussMat m k v =
      (m : ℝ) * v ^ 2 * (1 - dotp h h' ^ 2) ^ 2 := by
  obtain ⟨iP2, eP2⟩ := row_two hv (h + h')
  obtain ⟨iQ2, eQ2⟩ := row_two hv (h - h')
  obtain ⟨iP4, eP4⟩ := row_four hv (h + h')
  obtain ⟨iQ4, eQ4⟩ := row_four hv (h - h')
  obtain ⟨iU4, eU4⟩ := row_four hv h
  obtain ⟨iV4, eV4⟩ := row_four hv h'
  set τ := dotp h h' with hτ
  set f : (Fin k → ℝ) → ℝ := fun r =>
    dotp r h * dotp r h' - τ * ((dotp r h ^ 2 + dotp r h' ^ 2) / 2) with hfdef
  have hf : Measurable f :=
    ((measurable_dotp_left h).mul (measurable_dotp_left h')).sub
      (measurable_const.mul ((((measurable_dotp_left h).pow_const 2).add
        ((measurable_dotp_left h').pow_const 2)).div_const 2))
  have f1 : (fun ξ : Fin k → ℝ => f (Real.sqrt v • ξ)) = fun ξ =>
      (1 - τ) / 4 * dotp (Real.sqrt v • ξ) (h + h') ^ 2 + 0 -
        (1 + τ) / 4 * dotp (Real.sqrt v • ξ) (h - h') ^ 2 -
        0 * dotp (Real.sqrt v • ξ) (h - h') ^ 2 - 0 * dotp (Real.sqrt v • ξ) (h - h') ^ 2 := by
    funext ξ
    simp only [hfdef, dotp_add_right, dotp_sub_right]
    ring
  obtain ⟨-, m1⟩ := integral_lin4 (μ := stdGauss (Fin k)) iP2 iQ2 iQ2 iQ2 0
    ((1 - τ) / 4) ((1 + τ) / 4) 0 0
  have mean0 : ∫ ξ : Fin k → ℝ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) = 0 := by
    rw [f1, m1, eP2, eQ2, normSq_add, normSq_sub, hh, hh', ← hτ]
    ring
  have f2 : (fun ξ : Fin k → ℝ => f (Real.sqrt v • ξ) ^ 2) = fun ξ =>
      (((1 - τ) ^ 2 + (1 - τ ^ 2) / 3) / 16) * dotp (Real.sqrt v • ξ) (h + h') ^ 4 + 0 -
        -(((1 + τ) ^ 2 + (1 - τ ^ 2) / 3) / 16) * dotp (Real.sqrt v • ξ) (h - h') ^ 4 -
        ((1 - τ ^ 2) / 6) * dotp (Real.sqrt v • ξ) h ^ 4 -
        ((1 - τ ^ 2) / 6) * dotp (Real.sqrt v • ξ) h' ^ 4 := by
    funext ξ
    simp only [hfdef, dotp_add_right, dotp_sub_right]
    ring
  obtain ⟨i2, m2⟩ := integral_lin4 (μ := stdGauss (Fin k)) iP4 iQ4 iU4 iV4 0
    (((1 - τ) ^ 2 + (1 - τ ^ 2) / 3) / 16) (-(((1 + τ) ^ 2 + (1 - τ ^ 2) / 3) / 16))
    ((1 - τ ^ 2) / 6) ((1 - τ ^ 2) / 6)
  rw [← f2] at i2 m2
  obtain ⟨is, es⟩ := rows_sum_sq (m := m) v f hf i2
  have hsum : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (M.mulVec h) (M.mulVec h') -
        τ * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2) = ∑ i, f (rowOf i M) := by
    intro M
    simp only [hfdef, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div,
      Finset.sum_add_distrib]
    rfl
  simp_rw [hsum]
  refine ⟨is, ?_⟩
  rw [es, mean0, m2, eP4, eQ4, eU4, eV4, normSq_add, normSq_sub, hh, hh', ← hτ]
  ring

end BstLean.Part133

open BstLean.Part133 in
#print axioms lin_sq_four
open BstLean.Part133 in
#print axioms lin_dot_var
open BstLean.Part133 in
#print axioms lin_ctp_var
