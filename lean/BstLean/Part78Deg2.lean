import BstLean.Part78Defs2
import BstLean.Part78MeanA
import BstLean.Part46CharFn_Spectral
import BstLean.Part29GaussProd

/-!
# Part 78: the fourth moment of a Gaussian polynomial of degree `≤ 2`, constant `35/2`

`deg2Fourth : Deg2Fourth (35 / 2)`.
-/

namespace BstLean.Part78

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq qformι)
open BstLean.Part46

/-! ## One coordinate -/

/-- `X = β g + λ (g² − 1)`. -/
private def d2_X (β l : ℝ) (x : ℝ) : ℝ := β * x + l * (x ^ 2 - 1)

private lemma d2_powint (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x)
    (μ := gaussianReal 0 1) (by simp) k

private lemma d2_polyint (N : ℕ) (a : ℕ → ℝ) :
    ∫ x, (∑ k ∈ Finset.range N, a k * x ^ k) ∂gaussianReal 0 1 =
      ∑ k ∈ Finset.range N, a k * gaussMom k := by
  rw [integral_finsetSum _ fun k _ => (d2_powint k).const_mul _]
  exact Finset.sum_congr rfl fun k _ => by rw [integral_const_mul, gaussMom_eq]

private lemma d2_gm : gaussMom 0 = 1 ∧ gaussMom 1 = 0 ∧ gaussMom 2 = 1 ∧ gaussMom 3 = 0 ∧
    gaussMom 4 = 3 ∧ gaussMom 5 = 0 ∧ gaussMom 6 = 15 ∧ gaussMom 7 = 0 ∧ gaussMom 8 = 105 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [gaussMom, Nat.doubleFactorial, parity_simps]

private lemma d2_poly9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℝ) :
    ∫ x : ℝ, (a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4 + a5 * x ^ 5 + a6 * x ^ 6 +
      a7 * x ^ 7 + a8 * x ^ 8) ∂gaussianReal 0 1 = a0 + a2 + 3 * a4 + 15 * a6 + 105 * a8 := by
  have h : ∀ x : ℝ, (a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4 + a5 * x ^ 5 + a6 * x ^ 6 +
      a7 * x ^ 7 + a8 * x ^ 8) =
      ∑ k ∈ Finset.range 9, ([a0, a1, a2, a3, a4, a5, a6, a7, a8].getD k 0) * x ^ k := by
    intro x; simp [Finset.sum_range_succ]
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := d2_gm
  simp_rw [h]
  rw [d2_polyint]
  simp [Finset.sum_range_succ, g0, g1, g2, g3, g4, g5, g6, g7, g8]
  ring

private lemma d2_one1 (β l : ℝ) : ∫ x, d2_X β l x ∂gaussianReal 0 1 = 0 := by
  have h : ∀ x : ℝ, d2_X β l x = (-l) + β * x + l * x ^ 2 + 0 * x ^ 3 + 0 * x ^ 4 + 0 * x ^ 5 +
      0 * x ^ 6 + 0 * x ^ 7 + 0 * x ^ 8 := by
    intro x; unfold d2_X; ring
  simp_rw [h]
  rw [d2_poly9]; ring

private lemma d2_one2 (β l : ℝ) : ∫ x, d2_X β l x ^ 2 ∂gaussianReal 0 1 = β ^ 2 + 2 * l ^ 2 := by
  have h : ∀ x : ℝ, d2_X β l x ^ 2 = l ^ 2 + (-2 * β * l) * x + (β ^ 2 - 2 * l ^ 2) * x ^ 2 +
      (2 * β * l) * x ^ 3 + l ^ 2 * x ^ 4 + 0 * x ^ 5 +
      0 * x ^ 6 + 0 * x ^ 7 + 0 * x ^ 8 := by
    intro x; unfold d2_X; ring
  simp_rw [h]
  rw [d2_poly9]; ring

private lemma d2_one4 (β l : ℝ) : ∫ x, d2_X β l x ^ 4 ∂gaussianReal 0 1 =
    3 * β ^ 4 + 60 * β ^ 2 * l ^ 2 + 60 * l ^ 4 := by
  have h : ∀ x : ℝ, d2_X β l x ^ 4 = l ^ 4 + (-4 * β * l ^ 3) * x +
      (6 * β ^ 2 * l ^ 2 - 4 * l ^ 4) * x ^ 2 +
      (12 * β * l ^ 3 - 4 * β ^ 3 * l) * x ^ 3 + (β ^ 4 - 12 * β ^ 2 * l ^ 2 + 6 * l ^ 4) * x ^ 4 +
      (4 * β ^ 3 * l - 12 * β * l ^ 3) * x ^ 5 +
      (6 * β ^ 2 * l ^ 2 - 4 * l ^ 4) * x ^ 6 + (4 * β * l ^ 3) * x ^ 7 + l ^ 4 * x ^ 8 := by
    intro x; unfold d2_X; ring
  simp_rw [h]
  rw [d2_poly9]; ring

/-! ## Independent sums -/

private lemma d2_lin {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f1 f2 f3 f4 f5 : Ω → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (h3 : Integrable f3 μ)
    (h4 : Integrable f4 μ) (h5 : Integrable f5 μ) (a0 a1 a2 a3 a4 a5 : ℝ) :
    ∫ z, (a0 + a1 * f1 z + a2 * f2 z + a3 * f3 z + a4 * f4 z + a5 * f5 z) ∂μ =
      a0 + a1 * ∫ z, f1 z ∂μ + a2 * ∫ z, f2 z ∂μ + a3 * ∫ z, f3 z ∂μ + a4 * ∫ z, f4 z ∂μ +
        a5 * ∫ z, f5 z ∂μ := by
  have i0 : Integrable (fun _ : Ω => a0) μ := integrable_const _
  have i1 : Integrable (fun z => a0 + a1 * f1 z) μ := i0.add (h1.const_mul a1)
  have i2 : Integrable (fun z => a0 + a1 * f1 z + a2 * f2 z) μ := i1.add (h2.const_mul a2)
  have i3 : Integrable (fun z => a0 + a1 * f1 z + a2 * f2 z + a3 * f3 z) μ :=
    i2.add (h3.const_mul a3)
  have i4 : Integrable (fun z => a0 + a1 * f1 z + a2 * f2 z + a3 * f3 z + a4 * f4 z) μ :=
    i3.add (h4.const_mul a4)
  rw [integral_add i4 (h5.const_mul a5), integral_add i3 (h4.const_mul a4),
    integral_add i2 (h3.const_mul a3), integral_add i1 (h2.const_mul a2),
    integral_add i0 (h1.const_mul a1)]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul]

section core
variable {ι : Type*} [Fintype ι] (β l : ι → ℝ)

private def d2_f (i : ι) (z : ι → ℝ) : ℝ := d2_X (β i) (l i) (z i)

private def d2_U (s : Finset ι) (z : ι → ℝ) : ℝ := ∑ i ∈ s, d2_f β l i z

private lemma d2_coord (i : ι) (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ z, g (z i) ∂stdGauss ι = ∫ x, g x ∂gaussianReal 0 1 := by
  have hmp : MeasurePreserving (Function.eval i) (stdGauss ι) (gaussianReal 0 1) := by
    unfold stdGauss
    exact measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hg.aestronglyMeasurable]

private lemma d2_Xcont (b c : ℝ) : Continuous (d2_X b c) := by unfold d2_X; fun_prop

private lemma d2_f1 (i : ι) : ∫ z, d2_f β l i z ∂stdGauss ι = 0 := by
  unfold d2_f
  rw [d2_coord i _ (d2_Xcont _ _), d2_one1]

private lemma d2_f2 (i : ι) : ∫ z, d2_f β l i z ^ 2 ∂stdGauss ι = β i ^ 2 + 2 * l i ^ 2 := by
  unfold d2_f
  rw [d2_coord i (fun x => d2_X (β i) (l i) x ^ 2) ((d2_Xcont _ _).pow 2), d2_one2]

private lemma d2_f4 (i : ι) : ∫ z, d2_f β l i z ^ 4 ∂stdGauss ι =
    3 * β i ^ 4 + 60 * β i ^ 2 * l i ^ 2 + 60 * l i ^ 4 := by
  unfold d2_f
  rw [d2_coord i (fun x => d2_X (β i) (l i) x ^ 4) ((d2_Xcont _ _).pow 4), d2_one4]

private lemma d2_goodf (i : ι) : Good (stdGauss ι) (d2_f β l i) := by
  unfold d2_f d2_X
  exact ((good_coord i).const_mul _).add ((((good_coord i).pow 2).sub (Good.const 1)).const_mul _)

private lemma d2_goodU (s : Finset ι) : Good (stdGauss ι) (d2_U β l s) :=
  Good.sum s fun i _ => d2_goodf β l i

private lemma d2_indep (s : Finset ι) (i : ι) (hi : i ∉ s) (a b : ℕ) :
    ∫ z, d2_U β l s z ^ a * d2_f β l i z ^ b ∂stdGauss ι =
      (∫ z, d2_U β l s z ^ a ∂stdGauss ι) * ∫ z, d2_f β l i z ^ b ∂stdGauss ι := by
  have hind : iIndepFun (fun i (z : ι → ℝ) => d2_X (β i) (l i) (z i)) (stdGauss ι) := by
    unfold stdGauss
    exact iIndepFun_pi fun i => (d2_Xcont _ _).measurable.aemeasurable
  have hm : ∀ j, Measurable (fun z : ι → ℝ => d2_X (β j) (l j) (z j)) := fun j =>
    (d2_Xcont _ _).measurable.comp (measurable_pi_apply j)
  have h2 := hind.indepFun_finsetSum_of_notMem hm hi
  have h3 := h2.comp (measurable_id.pow_const a) (measurable_id.pow_const b)
  have hs : Measurable (∑ j ∈ s, fun z : ι → ℝ => d2_X (β j) (l j) (z j)) := by
    have he : (∑ j ∈ s, fun z : ι → ℝ => d2_X (β j) (l j) (z j)) =
        fun z => ∑ j ∈ s, d2_X (β j) (l j) (z j) := by ext z; simp
    rw [he]; exact Finset.measurable_sum s fun j _ => hm j
  have h4 := h3.integral_fun_mul_eq_mul_integral
    (((measurable_id.pow_const a).comp hs).aestronglyMeasurable)
    (((measurable_id.pow_const b).comp (hm i)).aestronglyMeasurable)
  simpa [Function.comp, Finset.sum_apply, d2_U, d2_f] using h4

private lemma d2_core (s : Finset ι) :
    ∫ z, d2_U β l s z ∂stdGauss ι = 0 ∧
    ∫ z, d2_U β l s z ^ 2 ∂stdGauss ι = ∑ i ∈ s, (β i ^ 2 + 2 * l i ^ 2) ∧
    ∫ z, d2_U β l s z ^ 4 ∂stdGauss ι ≤ 15 * (∑ i ∈ s, (β i ^ 2 + 2 * l i ^ 2)) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [d2_U]
  | insert i s hi ih =>
    obtain ⟨ih1, ih2, ih4⟩ := ih
    have hU : ∀ z, d2_U β l (insert i s) z = d2_U β l s z + d2_f β l i z := by
      intro z; unfold d2_U; rw [Finset.sum_insert hi, add_comm]
    have gU := d2_goodU β l s
    have gf := d2_goodf β l i
    have hI : ∀ a b : ℕ, Integrable (fun z => d2_U β l s z ^ a * d2_f β l i z ^ b) (stdGauss ι) :=
      fun a b => ((gU.pow a).mul (gf.pow b)).integrable
    have hind := d2_indep β l s i hi
    have hm0 : 0 ≤ ∑ j ∈ s, (β j ^ 2 + 2 * l j ^ 2) :=
      Finset.sum_nonneg fun j _ => by positivity
    have u1 : ∫ z, d2_U β l s z ^ 1 ∂stdGauss ι = 0 := by simpa using ih1
    have f1 : ∫ z, d2_f β l i z ^ 1 ∂stdGauss ι = 0 := by simpa using d2_f1 β l i
    have u0 : ∫ z, d2_U β l s z ^ 0 ∂stdGauss ι = 1 := by simp
    have f0 : ∫ z, d2_f β l i z ^ 0 ∂stdGauss ι = 1 := by simp
    simp_rw [hU, Finset.sum_insert hi]
    refine ⟨?_, ?_, ?_⟩
    · rw [integral_add gU.integrable gf.integrable, ih1, d2_f1, add_zero]
    · have e : ∀ z, (d2_U β l s z + d2_f β l i z) ^ 2 =
          0 + 1 * (d2_U β l s z ^ 2 * d2_f β l i z ^ 0) + 2 * (d2_U β l s z ^ 1 * d2_f β l i z ^ 1) +
            1 * (d2_U β l s z ^ 0 * d2_f β l i z ^ 2) + 0 * (d2_U β l s z ^ 0 * d2_f β l i z ^ 0) +
            0 * (d2_U β l s z ^ 0 * d2_f β l i z ^ 0) := fun z => by ring
      simp_rw [e]
      rw [d2_lin (hI _ _) (hI _ _) (hI _ _) (hI _ _) (hI _ _)]
      simp only [hind, u0, f0, u1, f1, ih2, d2_f2]
      ring
    · have e : ∀ z, (d2_U β l s z + d2_f β l i z) ^ 4 =
          0 + 1 * (d2_U β l s z ^ 4 * d2_f β l i z ^ 0) + 4 * (d2_U β l s z ^ 3 * d2_f β l i z ^ 1) +
            6 * (d2_U β l s z ^ 2 * d2_f β l i z ^ 2) + 4 * (d2_U β l s z ^ 1 * d2_f β l i z ^ 3) +
            1 * (d2_U β l s z ^ 0 * d2_f β l i z ^ 4) := fun z => by ring
      simp_rw [e]
      rw [d2_lin (hI _ _) (hI _ _) (hI _ _) (hI _ _) (hI _ _)]
      simp only [hind, u0, f0, u1, f1, ih2, d2_f2, d2_f4]
      have hv : 0 ≤ β i ^ 2 + 2 * l i ^ 2 := by positivity
      nlinarith [mul_nonneg hm0 hv, sq_nonneg (β i), sq_nonneg (l i),
        mul_nonneg (sq_nonneg (β i)) (sq_nonneg (l i)), sq_nonneg (β i ^ 2), sq_nonneg (l i ^ 2)]

/-- The constant term. -/
private lemma d2_final (c : ℝ) :
    ∫ z, (c + d2_U β l Finset.univ z) ^ 4 ∂stdGauss ι ≤
      35 / 2 * (∫ z, (c + d2_U β l Finset.univ z) ^ 2 ∂stdGauss ι) ^ 2 := by
  obtain ⟨h1, h2, h4⟩ := d2_core β l Finset.univ
  set U := d2_U β l Finset.univ with hUdef
  have gU : Good (stdGauss ι) U := d2_goodU β l Finset.univ
  set m := ∑ i, (β i ^ 2 + 2 * l i ^ 2) with hm
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun j _ => by positivity
  have hI : ∀ a : ℕ, Integrable (fun z => U z ^ a) (stdGauss ι) := fun a => (gU.pow a).integrable
  have u1 : ∫ z, U z ^ 1 ∂stdGauss ι = 0 := by simpa using h1
  set E3 := ∫ z, U z ^ 3 ∂stdGauss ι with hE3
  set E4 := ∫ z, U z ^ 4 ∂stdGauss ι with hE4
  have hq : 0 ≤ 196 * c ^ 2 * m - 28 * c * E3 + E4 := by
    have h : 0 ≤ ∫ z, ((-14 * c) * U z + U z ^ 2) ^ 2 ∂stdGauss ι :=
      integral_nonneg fun z => sq_nonneg _
    have e : ∀ z, ((-14 * c) * U z + U z ^ 2) ^ 2 =
        0 + (196 * c ^ 2) * U z ^ 2 + (-28 * c) * U z ^ 3 + 1 * U z ^ 4 + 0 * U z ^ 1 +
          0 * U z ^ 1 := fun z => by ring
    simp_rw [e] at h
    rw [d2_lin (hI _) (hI _) (hI _) (hI _) (hI _)] at h
    rw [h2] at h
    linarith
  have e2 : ∀ z, (c + U z) ^ 2 = c ^ 2 + (2 * c) * U z ^ 1 + 1 * U z ^ 2 + 0 * U z ^ 1 +
      0 * U z ^ 1 + 0 * U z ^ 1 := fun z => by ring
  have e4 : ∀ z, (c + U z) ^ 4 = c ^ 4 + (4 * c ^ 3) * U z ^ 1 + (6 * c ^ 2) * U z ^ 2 +
      (4 * c) * U z ^ 3 + 1 * U z ^ 4 + 0 * U z ^ 1 := fun z => by ring
  simp_rw [e2, e4]
  rw [d2_lin (hI _) (hI _) (hI _) (hI _) (hI _), d2_lin (hI _) (hI _) (hI _) (hI _) (hI _)]
  rw [u1, h2]
  nlinarith [sq_nonneg c, mul_nonneg (sq_nonneg c) hm0, sq_nonneg m, sq_nonneg (c ^ 2)]

end core

/-! ## The shape of a polynomial of degree `≤ 2` -/

section shape
set_option linter.unusedSectionVars false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma d2_split (m : ι →₀ ℕ) (hm : m ≠ 0) :
    ∃ (i : ι) (m' : ι →₀ ℕ), m = Finsupp.single i 1 + m' ∧ (∑ j, m' j) + 1 = ∑ j, m j := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (Finsupp.ext h)
  have he : m = Finsupp.single i 1 + (m - Finsupp.single i 1) := by
    ext j
    by_cases hj : i = j
    · subst hj; simp; omega
    · simp [hj]
  refine ⟨i, m - Finsupp.single i 1, he, ?_⟩
  conv_rhs => rw [he]
  simp [Finset.sum_add_distrib, Finsupp.single_apply, add_comm]

private lemma d2_zero (m : ι →₀ ℕ) (h : ∑ j, m j ≤ 0) : m = 0 := by
  ext j
  have := Finset.single_le_sum (f := fun j => m j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  omega

private lemma d2_step (i : ι) (m' : ι →₀ ℕ) (a : ℝ) (z : ι → ℝ) :
    MvPolynomial.eval z (MvPolynomial.monomial (Finsupp.single i 1 + m') a) =
      z i * MvPolynomial.eval z (MvPolynomial.monomial m' a) := by
  rw [MvPolynomial.monomial_single_add]; simp

private lemma d2_mon1 (m : ι →₀ ℕ) (a : ℝ) (h : ∑ j, m j ≤ 1) :
    ∃ (c : ℝ) (b : ι → ℝ), ∀ z : ι → ℝ,
      MvPolynomial.eval z (MvPolynomial.monomial m a) = c + ∑ j, b j * z j := by
  by_cases hm : m = 0
  · subst hm; exact ⟨a, 0, fun z => by simp⟩
  · obtain ⟨i, m', rfl, hd⟩ := d2_split m hm
    have h0 : m' = 0 := d2_zero m' (by omega)
    subst h0
    refine ⟨0, Pi.single i a, fun z => ?_⟩
    rw [d2_step]
    simp [Pi.single_apply, mul_comm]

private lemma d2_mon2 (m : ι →₀ ℕ) (a : ℝ) (h : ∑ j, m j ≤ 2) :
    ∃ (c : ℝ) (b : ι → ℝ) (A : ι → ι → ℝ), ∀ z : ι → ℝ,
      MvPolynomial.eval z (MvPolynomial.monomial m a) =
        c + ∑ j, b j * z j + ∑ j, ∑ k, A j k * z j * z k := by
  by_cases hm : m = 0
  · subst hm; exact ⟨a, 0, 0, fun z => by simp⟩
  · obtain ⟨i, m', rfl, hd⟩ := d2_split m hm
    obtain ⟨c, b, hb⟩ := d2_mon1 m' a (by omega)
    refine ⟨0, Pi.single i c, fun j k => if j = i then b k else 0, fun z => ?_⟩
    rw [d2_step, hb]
    simp [Pi.single_apply, ite_mul, Finset.mul_sum, mul_add]
    rw [mul_comm (z i) c]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring

private lemma d2_shape (P : MvPolynomial ι ℝ) (hP : P.totalDegree ≤ 2) :
    ∃ (c : ℝ) (b : ι → ℝ) (A : ι → ι → ℝ), ∀ z : ι → ℝ,
      MvPolynomial.eval z P = c + ∑ j, b j * z j + ∑ j, ∑ k, A j k * z j * z k := by
  have key : ∀ s : Finset (ι →₀ ℕ), (∀ m ∈ s, ∑ j, m j ≤ 2) →
      ∃ (c : ℝ) (b : ι → ℝ) (A : ι → ι → ℝ), ∀ z : ι → ℝ,
        MvPolynomial.eval z (∑ m ∈ s, MvPolynomial.monomial m (P.coeff m)) =
          c + ∑ j, b j * z j + ∑ j, ∑ k, A j k * z j * z k := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨0, 0, 0, fun z => by simp⟩
    | insert m s hm ih =>
      intro h
      obtain ⟨c, b, A, hs⟩ := ih fun m' hm' => h m' (Finset.mem_insert_of_mem hm')
      obtain ⟨c', b', A', hm'⟩ := d2_mon2 m (P.coeff m) (h m (Finset.mem_insert_self _ _))
      refine ⟨c' + c, fun j => b' j + b j, fun j k => A' j k + A j k, fun z => ?_⟩
      rw [Finset.sum_insert hm, map_add, hs, hm']
      simp only [add_mul, Finset.sum_add_distrib]
      ring
  have h := key P.support fun m hm => by
    have := (MvPolynomial.le_totalDegree hm).trans hP
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
  rwa [← P.as_sum] at h

end shape

/-! ## The theorem -/

/-- **Fourth moment at degree two**: `E P⁴ ≤ (35/2) (E P²)²`. -/
theorem deg2Fourth : Deg2Fourth (35 / 2) := by
  intro ι _ P hP
  classical
  obtain ⟨c, b, A, hPz⟩ := d2_shape P hP
  let S : Matrix ι ι ℝ := fun i j => (A i j + A j i) / 2
  have hS : S.IsHermitian := by
    ext i j
    simp [S, Matrix.conjTranspose, Matrix.transpose, add_comm]
  let B := hS.eigenvectorBasis
  let beta : ι → ℝ := fun i => B.repr (WithLp.toLp 2 b) i
  let T : (ι → ℝ) → (ι → ℝ) := fun z => WithLp.ofLp (B.repr (WithLp.toLp 2 z))
  have hsym (z : ι → ℝ) : (∑ i, ∑ j, A i j * z i * z j) = qformι S z := by
    unfold qformι
    have hswap : (∑ i, ∑ j, A j i * z i * z j) = ∑ i, ∑ j, A i j * z i * z j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hp (i j : ι) : S i j * z i * z j =
        (A i j * z i * z j + A j i * z i * z j) / 2 := by simp only [S]; ring
    simp_rw [hp, ← Finset.sum_div, Finset.sum_add_distrib]
    rw [hswap]
    ring
  have hq (z : ι → ℝ) : MvPolynomial.eval z P =
      (c + ∑ i, hS.eigenvalues i) + d2_U beta hS.eigenvalues Finset.univ (T z) := by
    rw [hPz, hsym, CharFn.qform_eigenbasis S hS, CharFn.linear_eigenbasis B b z]
    simp only [d2_U, d2_f, d2_X, T, beta, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      mul_one]
    ring
  have hp := CharFn.gaussian_basis_preserving B
  have hemb : MeasurableEmbedding T :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding.comp
      (B.repr.toHomeomorph.measurableEmbedding.comp
        (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding)
  simp_rw [hq]
  rw [hp.integral_comp hemb (fun y : ι → ℝ =>
      ((c + ∑ i, hS.eigenvalues i) + d2_U beta hS.eigenvalues Finset.univ y) ^ 4),
    hp.integral_comp hemb (fun y : ι → ℝ =>
      ((c + ∑ i, hS.eigenvalues i) + d2_U beta hS.eigenvalues Finset.univ y) ^ 2)]
  exact d2_final beta hS.eigenvalues _

end BstLean.Part78

#print axioms BstLean.Part78.deg2Fourth
