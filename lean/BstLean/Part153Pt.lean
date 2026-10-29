import BstLean.Part130Moments

/-!
# Part 153, the norm of one ReLU layer at a fixed input

Compare the "fixed input" paragraph of the proof of Lemma N in
`proofs/option-n/theorem5-07-norms.tex`.

For a Gaussian matrix `M` (`m` rows, entries of variance `v > 0`) and a fixed vector `a ≠ 0`, let
`s = √((m/2)·v|a|²)`. Then

* `relu_norm_dev2`: `E(|ReLU(M a)|/s − 1)² ≤ 5/m`;
* `relu_norm_dev4`: `E(|ReLU(M a)|/s − 1)⁴ ≤ 75/m² + 558/m³`.

The same statements for `ξ` standard Gaussian in `ℝ^m` and `X = (2/m)·Σ_i ReLU(ξ_i)²`:
`relu_std_dev2`, `relu_std_dev4`. The exact moments of `X − 1` are in `relu_std_core`.

The general tool is `pi_finset_moments`: for independent copies of a centred variable,
`E(Σ_{i∈s} c_i)² = |s|·σ²` and `E(Σ_{i∈s} c_i)⁴ = |s|·μ₄ + 3|s|(|s| − 1)·σ⁴`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part130
open scoped Matrix

/-! ## Sums of integrable functions -/

section generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma int_add3 {A B C : Ω → ℝ} (hA : Integrable A P) (hB : Integrable B P) (hC : Integrable C P) :
    Integrable (fun ω => A ω + B ω + C ω) P ∧
    ∫ ω, (A ω + B ω + C ω) ∂P = ∫ ω, A ω ∂P + ∫ ω, B ω ∂P + ∫ ω, C ω ∂P := by
  have hAB : Integrable (fun ω => A ω + B ω) P := hA.add hB
  exact ⟨hAB.add hC, by rw [integral_add hAB hC, integral_add hA hB]⟩

lemma int_add4 {A B C D : Ω → ℝ} (hA : Integrable A P) (hB : Integrable B P)
    (hC : Integrable C P) (hD : Integrable D P) :
    Integrable (fun ω => A ω + B ω + C ω + D ω) P ∧
    ∫ ω, (A ω + B ω + C ω + D ω) ∂P =
      ∫ ω, A ω ∂P + ∫ ω, B ω ∂P + ∫ ω, C ω ∂P + ∫ ω, D ω ∂P := by
  obtain ⟨h3, e3⟩ := int_add3 hA hB hC
  exact ⟨h3.add hD, by rw [integral_add h3 hD, e3]⟩

lemma int_add5 {A B C D E : Ω → ℝ} (hA : Integrable A P) (hB : Integrable B P)
    (hC : Integrable C P) (hD : Integrable D P) (hE : Integrable E P) :
    Integrable (fun ω => A ω + B ω + C ω + D ω + E ω) P ∧
    ∫ ω, (A ω + B ω + C ω + D ω + E ω) ∂P =
      ∫ ω, A ω ∂P + ∫ ω, B ω ∂P + ∫ ω, C ω ∂P + ∫ ω, D ω ∂P + ∫ ω, E ω ∂P := by
  obtain ⟨h4, e4⟩ := int_add4 hA hB hC hD
  exact ⟨h4.add hE, by rw [integral_add h4 hE, e4]⟩

/-! ## Two independent centred variables -/

lemma indep_mul {U V : Ω → ℝ} (h : IndepFun U V P) (hU : Integrable U P) (hV : Integrable V P) :
    Integrable (fun ω => U ω * V ω) P ∧
    ∫ ω, U ω * V ω ∂P = (∫ ω, U ω ∂P) * ∫ ω, V ω ∂P :=
  ⟨h.integrable_mul hU hV,
    h.integral_fun_mul_eq_mul_integral hU.aestronglyMeasurable hV.aestronglyMeasurable⟩

/-- Moments up to order four of the sum of two independent centred variables. -/
lemma indep_add_moments {X Y : Ω → ℝ} (h : IndepFun X Y P)
    (hX1 : Integrable X P) (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (hX3 : Integrable (fun ω => X ω ^ 3) P) (hX4 : Integrable (fun ω => X ω ^ 4) P)
    (hY1 : Integrable Y P) (hY2 : Integrable (fun ω => Y ω ^ 2) P)
    (hY3 : Integrable (fun ω => Y ω ^ 3) P) (hY4 : Integrable (fun ω => Y ω ^ 4) P)
    (eX : ∫ ω, X ω ∂P = 0) (eY : ∫ ω, Y ω ∂P = 0) :
    Integrable (fun ω => X ω + Y ω) P ∧ Integrable (fun ω => (X ω + Y ω) ^ 2) P ∧
    Integrable (fun ω => (X ω + Y ω) ^ 3) P ∧ Integrable (fun ω => (X ω + Y ω) ^ 4) P ∧
    ∫ ω, (X ω + Y ω) ∂P = 0 ∧
    ∫ ω, (X ω + Y ω) ^ 2 ∂P = ∫ ω, X ω ^ 2 ∂P + ∫ ω, Y ω ^ 2 ∂P ∧
    ∫ ω, (X ω + Y ω) ^ 4 ∂P =
      ∫ ω, X ω ^ 4 ∂P + 6 * ((∫ ω, X ω ^ 2 ∂P) * ∫ ω, Y ω ^ 2 ∂P) + ∫ ω, Y ω ^ 4 ∂P := by
  have i21 : IndepFun (fun ω => X ω ^ 2) Y P :=
    h.comp (φ := fun x : ℝ => x ^ 2) (ψ := id) (by fun_prop) measurable_id
  have i12 : IndepFun X (fun ω => Y ω ^ 2) P :=
    h.comp (φ := id) (ψ := fun x : ℝ => x ^ 2) measurable_id (by fun_prop)
  have i31 : IndepFun (fun ω => X ω ^ 3) Y P :=
    h.comp (φ := fun x : ℝ => x ^ 3) (ψ := id) (by fun_prop) measurable_id
  have i13 : IndepFun X (fun ω => Y ω ^ 3) P :=
    h.comp (φ := id) (ψ := fun x : ℝ => x ^ 3) measurable_id (by fun_prop)
  have i22 : IndepFun (fun ω => X ω ^ 2) (fun ω => Y ω ^ 2) P :=
    h.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2) (by fun_prop) (by fun_prop)
  have p11 := indep_mul h hX1 hY1
  have p21 := indep_mul i21 hX2 hY1
  have p12 := indep_mul i12 hX1 hY2
  have p31 := indep_mul i31 hX3 hY1
  have p13 := indep_mul i13 hX1 hY3
  have p22 := indep_mul i22 hX2 hY2
  have e2 : (fun ω => (X ω + Y ω) ^ 2) = fun ω => X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2 := by
    funext ω; ring
  have e3 : (fun ω => (X ω + Y ω) ^ 3) =
      fun ω => X ω ^ 3 + 3 * (X ω ^ 2 * Y ω) + 3 * (X ω * Y ω ^ 2) + Y ω ^ 3 := by
    funext ω; ring
  have e4 : (fun ω => (X ω + Y ω) ^ 4) =
      fun ω => X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 6 * (X ω ^ 2 * Y ω ^ 2) + 4 * (X ω * Y ω ^ 3)
        + Y ω ^ 4 := by
    funext ω; ring
  have b11 : Integrable (fun ω => 2 * (X ω * Y ω)) P := p11.1.const_mul 2
  have b21 : Integrable (fun ω => 3 * (X ω ^ 2 * Y ω)) P := p21.1.const_mul 3
  have b12 : Integrable (fun ω => 3 * (X ω * Y ω ^ 2)) P := p12.1.const_mul 3
  have b31 : Integrable (fun ω => 4 * (X ω ^ 3 * Y ω)) P := p31.1.const_mul 4
  have b22 : Integrable (fun ω => 6 * (X ω ^ 2 * Y ω ^ 2)) P := p22.1.const_mul 6
  have b13 : Integrable (fun ω => 4 * (X ω * Y ω ^ 3)) P := p13.1.const_mul 4
  obtain ⟨j2, v2⟩ := int_add3 hX2 b11 hY2
  obtain ⟨j3, -⟩ := int_add4 hX3 b21 b12 hY3
  obtain ⟨j4, v4⟩ := int_add5 hX4 b31 b22 b13 hY4
  refine ⟨hX1.add hY1, by rw [e2]; exact j2, by rw [e3]; exact j3, by rw [e4]; exact j4,
    ?_, ?_, ?_⟩
  · rw [integral_add hX1 hY1, eX, eY, add_zero]
  · rw [e2, v2, integral_const_mul, p11.2, eX, eY]; ring
  · rw [e4, v4, integral_const_mul, integral_const_mul, integral_const_mul, p31.2, p22.2,
      p13.2, eX, eY]; ring

end generic

/-! ## Sums of independent copies of a centred variable -/

section pi

variable {ι : Type*} [Fintype ι] {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- For independent copies `f(ω_i)` of a centred variable (`E f = 0`) and a finite set `s` of
indices: `E(Σ_{i∈s} f(ω_i))² = |s|·E f²` and
`E(Σ_{i∈s} f(ω_i))⁴ = |s|·E f⁴ + 3|s|(|s| − 1)·(E f²)²`. -/
theorem pi_finset_moments {f : ℝ → ℝ} (hfm : Measurable f) (hf1 : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hf3 : Integrable (fun x => f x ^ 3) μ)
    (hf4 : Integrable (fun x => f x ^ 4) μ) (e0 : ∫ x, f x ∂μ = 0) (s : Finset ι) :
    Integrable (fun ω : ι → ℝ => ∑ i ∈ s, f (ω i)) (Measure.pi fun _ : ι => μ) ∧
    Integrable (fun ω : ι → ℝ => (∑ i ∈ s, f (ω i)) ^ 2) (Measure.pi fun _ : ι => μ) ∧
    Integrable (fun ω : ι → ℝ => (∑ i ∈ s, f (ω i)) ^ 3) (Measure.pi fun _ : ι => μ) ∧
    Integrable (fun ω : ι → ℝ => (∑ i ∈ s, f (ω i)) ^ 4) (Measure.pi fun _ : ι => μ) ∧
    ∫ ω : ι → ℝ, ∑ i ∈ s, f (ω i) ∂(Measure.pi fun _ : ι => μ) = 0 ∧
    ∫ ω : ι → ℝ, (∑ i ∈ s, f (ω i)) ^ 2 ∂(Measure.pi fun _ : ι => μ) =
      s.card * ∫ x, f x ^ 2 ∂μ ∧
    ∫ ω : ι → ℝ, (∑ i ∈ s, f (ω i)) ^ 4 ∂(Measure.pi fun _ : ι => μ) =
      s.card * ∫ x, f x ^ 4 ∂μ + 3 * s.card * ((s.card : ℝ) - 1) * (∫ x, f x ^ 2 ∂μ) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨y1, y2, y3, y4, ey, ey2, ey4⟩ := ih
    have x1 : Integrable (fun ω : ι → ℝ => f (ω a)) (Measure.pi fun _ : ι => μ) :=
      integrable_comp_eval (μ := fun _ : ι => μ) (i := a) hf1
    have x2 : Integrable (fun ω : ι → ℝ => f (ω a) ^ 2) (Measure.pi fun _ : ι => μ) :=
      integrable_comp_eval (μ := fun _ : ι => μ) (i := a) hf2
    have x3 : Integrable (fun ω : ι → ℝ => f (ω a) ^ 3) (Measure.pi fun _ : ι => μ) :=
      integrable_comp_eval (μ := fun _ : ι => μ) (i := a) hf3
    have x4 : Integrable (fun ω : ι → ℝ => f (ω a) ^ 4) (Measure.pi fun _ : ι => μ) :=
      integrable_comp_eval (μ := fun _ : ι => μ) (i := a) hf4
    have ex : ∫ ω : ι → ℝ, f (ω a) ∂(Measure.pi fun _ : ι => μ) = 0 := by
      rw [integral_comp_eval (μ := fun _ : ι => μ) (i := a) hf1.aestronglyMeasurable, e0]
    have ex2 : ∫ ω : ι → ℝ, f (ω a) ^ 2 ∂(Measure.pi fun _ : ι => μ) = ∫ x, f x ^ 2 ∂μ :=
      integral_comp_eval (μ := fun _ : ι => μ) (i := a) hf2.aestronglyMeasurable
    have ex4 : ∫ ω : ι → ℝ, f (ω a) ^ 4 ∂(Measure.pi fun _ : ι => μ) = ∫ x, f x ^ 4 ∂μ :=
      integral_comp_eval (μ := fun _ : ι => μ) (i := a) hf4.aestronglyMeasurable
    have hind : IndepFun (fun ω : ι → ℝ => f (ω a)) (fun ω : ι → ℝ => ∑ i ∈ s, f (ω i))
        (Measure.pi fun _ : ι => μ) := by
      have h0 := (iIndepFun_pi (μ := fun _ : ι => μ) (X := fun _ => f)
        (fun _ => hfm.aemeasurable)).indepFun_finsetSum_of_notMem
        (fun i => hfm.comp (measurable_pi_apply i)) ha
      have e : (∑ j ∈ s, fun ω : ι → ℝ => f (ω j)) = fun ω : ι → ℝ => ∑ i ∈ s, f (ω i) := by
        funext ω; simp [Finset.sum_apply]
      have h1 : IndepFun (∑ j ∈ s, fun ω : ι → ℝ => f (ω j)) (fun ω : ι → ℝ => f (ω a))
          (Measure.pi fun _ : ι => μ) := h0
      rw [e] at h1
      exact h1.symm
    obtain ⟨z1, z2, z3, z4, ez, ez2, ez4⟩ :=
      indep_add_moments hind x1 x2 x3 x4 y1 y2 y3 y4 ex ey
    simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    refine ⟨z1, z2, z3, z4, ez, ?_, ?_⟩
    · rw [ez2, ex2, ey2]; push_cast; ring
    · rw [ez4, ex4, ex2, ey2, ey4]; push_cast; ring

end pi

/-! ## The centred variable `ReLU(g)² − 1/2` -/

lemma int_relu_six : ∫ x, relu x ^ 6 ∂gaussianReal 0 1 = 15 / 2 := by
  rw [int_relu_pow_even (by norm_num) (by decide)]
  have : Even 6 := by decide
  simp [gaussMom, this, Nat.doubleFactorial]

lemma int_relu_eight : ∫ x, relu x ^ 8 ∂gaussianReal 0 1 = 105 / 2 := by
  rw [int_relu_pow_even (by norm_num) (by decide)]
  have : Even 8 := by decide
  simp [gaussMom, this, Nat.doubleFactorial]

/-- The mean of an even polynomial of degree at most `8` in `ReLU(g)`. -/
lemma relu_comb (c8 c6 c4 c2 c0 : ℝ) :
    Integrable (fun x : ℝ => c8 * relu x ^ 8 + c6 * relu x ^ 6 + c4 * relu x ^ 4
      + c2 * relu x ^ 2 + c0) (gaussianReal 0 1) ∧
    ∫ x, (c8 * relu x ^ 8 + c6 * relu x ^ 6 + c4 * relu x ^ 4 + c2 * relu x ^ 2 + c0)
      ∂gaussianReal 0 1 = c8 * (105 / 2) + c6 * (15 / 2) + c4 * (3 / 2) + c2 * (1 / 2) + c0 := by
  obtain ⟨h, e⟩ := int_add5 ((integrable_relu_pow 8).const_mul c8)
    ((integrable_relu_pow 6).const_mul c6) ((integrable_relu_pow 4).const_mul c4)
    ((integrable_relu_pow 2).const_mul c2)
    (integrable_const c0 : Integrable (fun _ : ℝ => c0) (gaussianReal 0 1))
  refine ⟨h, ?_⟩
  rw [e, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    int_relu_eight, int_relu_six, int_relu_four, int_relu_sq]
  simp

lemma relu_comb' {g : ℝ → ℝ} (c8 c6 c4 c2 c0 : ℝ)
    (hg : ∀ x, g x = c8 * relu x ^ 8 + c6 * relu x ^ 6 + c4 * relu x ^ 4 + c2 * relu x ^ 2 + c0) :
    Integrable g (gaussianReal 0 1) ∧
    ∫ x, g x ∂gaussianReal 0 1 =
      c8 * (105 / 2) + c6 * (15 / 2) + c4 * (3 / 2) + c2 * (1 / 2) + c0 := by
  have : g = fun x : ℝ => c8 * relu x ^ 8 + c6 * relu x ^ 6 + c4 * relu x ^ 4
      + c2 * relu x ^ 2 + c0 := funext hg
  subst this
  exact relu_comb c8 c6 c4 c2 c0

/-- `ReLU(y)² − 1/2`: mean zero under the standard Gaussian. -/
noncomputable def cY (y : ℝ) : ℝ := relu y ^ 2 - 1 / 2

lemma measurable_cY : Measurable cY := (measurable_relu.pow_const 2).sub_const _

/-- `E c = 0`, `E c² = 5/4`, `E c⁴ = 633/16` for `c = ReLU(g)² − 1/2`. -/
lemma cY_moments :
    Integrable cY (gaussianReal 0 1) ∧ Integrable (fun x => cY x ^ 2) (gaussianReal 0 1) ∧
    Integrable (fun x => cY x ^ 3) (gaussianReal 0 1) ∧
    Integrable (fun x => cY x ^ 4) (gaussianReal 0 1) ∧
    ∫ x, cY x ∂gaussianReal 0 1 = 0 ∧ ∫ x, cY x ^ 2 ∂gaussianReal 0 1 = 5 / 4 ∧
    ∫ x, cY x ^ 4 ∂gaussianReal 0 1 = 633 / 16 := by
  obtain ⟨h1, e1⟩ := relu_comb' (g := cY) 0 0 0 1 (-1 / 2) (fun x => by simp only [cY]; ring)
  obtain ⟨h2, e2⟩ := relu_comb' (g := fun x => cY x ^ 2) 0 0 1 (-1) (1 / 4)
    (fun x => by simp only [cY]; ring)
  obtain ⟨h3, -⟩ := relu_comb' (g := fun x => cY x ^ 3) 0 1 (-3 / 2) (3 / 4) (-1 / 8)
    (fun x => by simp only [cY]; ring)
  obtain ⟨h4, e4⟩ := relu_comb' (g := fun x => cY x ^ 4) 1 (-2) (3 / 2) (-1 / 2) (1 / 16)
    (fun x => by simp only [cY]; ring)
  exact ⟨h1, h2, h3, h4, e1.trans (by norm_num), e2.trans (by norm_num), e4.trans (by norm_num)⟩

/-! ## The normalized squared norm under the standard Gaussian -/

lemma sqrt_dev_sq_le {X : ℝ} (hX : 0 ≤ X) : (√X - 1) ^ 2 ≤ (X - 1) ^ 2 := by
  have ht := Real.sqrt_nonneg X
  have h1 : 1 ≤ (√X + 1) ^ 2 := one_le_pow₀ (by linarith)
  calc (√X - 1) ^ 2 = (√X - 1) ^ 2 * 1 := by ring
    _ ≤ (√X - 1) ^ 2 * (√X + 1) ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (√X ^ 2 - 1) ^ 2 := by ring
    _ = (X - 1) ^ 2 := by rw [Real.sq_sqrt hX]

lemma sqrt_dev_four_le {X : ℝ} (hX : 0 ≤ X) : (√X - 1) ^ 4 ≤ (X - 1) ^ 4 := by
  have ht := Real.sqrt_nonneg X
  have h1 : 1 ≤ (√X + 1) ^ 4 := one_le_pow₀ (by linarith)
  calc (√X - 1) ^ 4 = (√X - 1) ^ 4 * 1 := by ring
    _ ≤ (√X - 1) ^ 4 * (√X + 1) ^ 4 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (√X ^ 2 - 1) ^ 4 := by ring
    _ = (X - 1) ^ 4 := by rw [Real.sq_sqrt hX]

lemma X_sub_one {m : ℕ} (hm : 1 ≤ m) (ξ : Fin m → ℝ) :
    2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2 - 1 = 2 / (m : ℝ) * ∑ i, cY (ξ i) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : 2 / (m : ℝ) * ((m : ℝ) * (1 / 2)) = 1 := by
    rw [div_mul_eq_mul_div, div_eq_iff hm']; ring
  simp only [cY, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [mul_sub, h2]

lemma meas_X (m : ℕ) : Measurable (fun ξ : Fin m → ℝ => 2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2) :=
  (measurable_normSq.comp measurable_reluV).const_mul _

lemma X_nonneg {m : ℕ} (ξ : Fin m → ℝ) : 0 ≤ 2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2 :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- **The exact second and fourth central moments** of `X = (2/m)·Σ_i ReLU(ξ_i)²`, `ξ` standard
Gaussian in `ℝ^m`: `E(X − 1)² = 5/m` and `E(X − 1)⁴ = 75/m² + 558/m³`. -/
theorem relu_std_core {m : ℕ} (hm : 1 ≤ m) :
    Integrable (fun ξ : Fin m → ℝ => (2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2 - 1) ^ 2)
      (stdGauss (Fin m)) ∧
    Integrable (fun ξ : Fin m → ℝ => (2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2 - 1) ^ 4)
      (stdGauss (Fin m)) ∧
    ∫ ξ : Fin m → ℝ, (2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2 - 1) ^ 2 ∂stdGauss (Fin m) =
      5 / (m : ℝ) ∧
    ∫ ξ : Fin m → ℝ, (2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2 - 1) ^ 4 ∂stdGauss (Fin m) =
      75 / (m : ℝ) ^ 2 + 558 / (m : ℝ) ^ 3 := by
  obtain ⟨c1, c2, c3, c4, e0, e2, e4⟩ := cY_moments
  obtain ⟨-, t2, -, t4, -, v2, v4⟩ :=
    pi_finset_moments (ι := Fin m) measurable_cY c1 c2 c3 c4 e0 Finset.univ
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have q2 : (fun ξ : Fin m → ℝ => (2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2 - 1) ^ 2) =
      fun ξ => (2 / (m : ℝ)) ^ 2 * (∑ i, cY (ξ i)) ^ 2 := by
    funext ξ; rw [X_sub_one hm, mul_pow]
  have q4 : (fun ξ : Fin m → ℝ => (2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2 - 1) ^ 4) =
      fun ξ => (2 / (m : ℝ)) ^ 4 * (∑ i, cY (ξ i)) ^ 4 := by
    funext ξ; rw [X_sub_one hm, mul_pow]
  unfold stdGauss
  rw [q2, q4]
  refine ⟨t2.const_mul _, t4.const_mul _, ?_, ?_⟩
  · rw [integral_const_mul, v2, e2, Finset.card_univ, Fintype.card_fin]
    field_simp
    ring
  · rw [integral_const_mul, v4, e4, e2, Finset.card_univ, Fintype.card_fin]
    field_simp
    ring

/-- `E(√X − 1)² ≤ 5/m` for `X = (2/m)·Σ_i ReLU(ξ_i)²`, `ξ` standard Gaussian in `ℝ^m`. -/
theorem relu_std_dev2 {m : ℕ} (hm : 1 ≤ m) :
    Integrable (fun ξ : Fin m → ℝ => (√(2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2) - 1) ^ 2)
      (stdGauss (Fin m)) ∧
    ∫ ξ : Fin m → ℝ, (√(2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2) - 1) ^ 2 ∂stdGauss (Fin m) ≤
      5 / (m : ℝ) := by
  obtain ⟨i2, -, v2, -⟩ := relu_std_core hm
  have hi : Integrable (fun ξ : Fin m → ℝ => (√(2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2) - 1) ^ 2)
      (stdGauss (Fin m)) := by
    refine i2.mono' (((meas_X m).sqrt.sub_const 1).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact sqrt_dev_sq_le (X_nonneg ξ)
  exact ⟨hi, (integral_mono hi i2 fun ξ => sqrt_dev_sq_le (X_nonneg ξ)).trans v2.le⟩

/-- `E(√X − 1)⁴ ≤ 75/m² + 558/m³` for `X = (2/m)·Σ_i ReLU(ξ_i)²`, `ξ` standard Gaussian in
`ℝ^m`. -/
theorem relu_std_dev4 {m : ℕ} (hm : 1 ≤ m) :
    Integrable (fun ξ : Fin m → ℝ => (√(2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2) - 1) ^ 4)
      (stdGauss (Fin m)) ∧
    ∫ ξ : Fin m → ℝ, (√(2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2) - 1) ^ 4 ∂stdGauss (Fin m) ≤
      75 / (m : ℝ) ^ 2 + 558 / (m : ℝ) ^ 3 := by
  obtain ⟨-, i4, -, v4⟩ := relu_std_core hm
  have hi : Integrable (fun ξ : Fin m → ℝ => (√(2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2) - 1) ^ 4)
      (stdGauss (Fin m)) := by
    refine i4.mono' (((meas_X m).sqrt.sub_const 1).pow_const 4).aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact sqrt_dev_four_le (X_nonneg ξ)
  exact ⟨hi, (integral_mono hi i4 fun ξ => sqrt_dev_four_le (X_nonneg ξ)).trans v4.le⟩

/-! ## One layer at a fixed input -/

/-- The normalized norm of `ReLU(c·ξ)`, `c = √v·|a|`, is `√X` with `X = (2/m)·Σ_i ReLU(ξ_i)²`. -/
lemma scaled_eq {m k : ℕ} (hm : 1 ≤ m) {v : ℝ} (hv : 0 < v) {a : Fin k → ℝ}
    (ha : 0 < normSq a) (ξ : Fin m → ℝ) :
    √(normSq (reluV ((√v * √(normSq a)) • ξ))) / √((m : ℝ) / 2 * (v * normSq a)) =
      √(2 / (m : ℝ) * ∑ i, relu (ξ i) ^ 2) := by
  have hmp : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hq : 0 < v * normSq a := mul_pos hv ha
  have hpos : 0 < (m : ℝ) / 2 * (v * normSq a) := mul_pos (div_pos hmp two_pos) hq
  rw [reluV_smul_of_nonneg (scale_nonneg v a), normSq_smul, sq_scale hv.le,
    ← Real.sqrt_div' _ hpos.le]
  congr 1
  show v * normSq a * normSq (reluV ξ) / ((m : ℝ) / 2 * (v * normSq a)) =
    2 / (m : ℝ) * normSq (reluV ξ)
  rw [div_eq_iff hpos.ne']
  have h2 : 2 / (m : ℝ) * ((m : ℝ) / 2) = 1 := by
    rw [div_mul_div_comm, div_eq_iff (mul_pos hmp two_pos).ne']; ring
  calc v * normSq a * normSq (reluV ξ)
      = (2 / (m : ℝ) * ((m : ℝ) / 2)) * (v * normSq a * normSq (reluV ξ)) := by
        rw [h2, one_mul]
    _ = 2 / (m : ℝ) * normSq (reluV ξ) * ((m : ℝ) / 2 * (v * normSq a)) := by ring

/-- **Second moment of the deviation of the normalized norm** of one ReLU layer at a fixed input
`a ≠ 0`: `E(|ReLU(M a)|/s − 1)² ≤ 5/m`, `s = √((m/2)·v|a|²)`. -/
theorem relu_norm_dev2 {m k : ℕ} (hm : 1 ≤ m) {v : ℝ} (hv : 0 < v) {a : Fin k → ℝ}
    (ha : 0 < normSq a) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
        (√(normSq (reluV (M *ᵥ a))) / √((m : ℝ) / 2 * (v * normSq a)) - 1) ^ 2)
      (gaussMat m k v) ∧
    ∫ M, (√(normSq (reluV (M *ᵥ a))) / √((m : ℝ) / 2 * (v * normSq a)) - 1) ^ 2
      ∂gaussMat m k v ≤ 5 / (m : ℝ) := by
  obtain ⟨hi, hb⟩ := relu_std_dev2 hm
  have hg : Measurable (fun y : Fin m → ℝ =>
      (√(normSq (reluV y)) / √((m : ℝ) / 2 * (v * normSq a)) - 1) ^ 2) :=
    ((((measurable_normSq.comp measurable_reluV).sqrt).div_const _).sub_const 1).pow_const 2
  refine ⟨layer_transfer_integrable v a hg ?_, ?_⟩
  · simp only [scaled_eq hm hv ha]; exact hi
  · rw [layer_transfer v a hg]; simp only [scaled_eq hm hv ha]; exact hb

/-- **Fourth moment of the deviation of the normalized norm** of one ReLU layer at a fixed input
`a ≠ 0`: `E(|ReLU(M a)|/s − 1)⁴ ≤ 75/m² + 558/m³`, `s = √((m/2)·v|a|²)`. -/
theorem relu_norm_dev4 {m k : ℕ} (hm : 1 ≤ m) {v : ℝ} (hv : 0 < v) {a : Fin k → ℝ}
    (ha : 0 < normSq a) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
        (√(normSq (reluV (M *ᵥ a))) / √((m : ℝ) / 2 * (v * normSq a)) - 1) ^ 4)
      (gaussMat m k v) ∧
    ∫ M, (√(normSq (reluV (M *ᵥ a))) / √((m : ℝ) / 2 * (v * normSq a)) - 1) ^ 4
      ∂gaussMat m k v ≤ 75 / (m : ℝ) ^ 2 + 558 / (m : ℝ) ^ 3 := by
  obtain ⟨hi, hb⟩ := relu_std_dev4 hm
  have hg : Measurable (fun y : Fin m → ℝ =>
      (√(normSq (reluV y)) / √((m : ℝ) / 2 * (v * normSq a)) - 1) ^ 4) :=
    ((((measurable_normSq.comp measurable_reluV).sqrt).div_const _).sub_const 1).pow_const 4
  refine ⟨layer_transfer_integrable v a hg ?_, ?_⟩
  · simp only [scaled_eq hm hv ha]; exact hi
  · rw [layer_transfer v a hg]; simp only [scaled_eq hm hv ha]; exact hb

end BstLean.Part153

#print axioms BstLean.Part153.pi_finset_moments
#print axioms BstLean.Part153.relu_std_core
#print axioms BstLean.Part153.relu_std_dev2
#print axioms BstLean.Part153.relu_std_dev4
#print axioms BstLean.Part153.relu_norm_dev2
#print axioms BstLean.Part153.relu_norm_dev4
