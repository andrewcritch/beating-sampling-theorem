import BstLean.Part56Key
import BstLean.Part56PropD
import BstLean.Part62Kappa5

/-!
# Part 64: explicit Key Lemma and Prop D constants for Theorem 1 (rank one)

* `kcrit5_2`, `fourth_moment_5_2`: `E P⁴ ≤ 5⁴ (E P²)²` for degree `≤ 2` (`κ = 5`, `Part62Kappa5.γ5`).
* `qrad_fourth64`: the fourth central moment of `qrad56` with `K₂ = 5⁴` (replaces
  `Part56.qrad_fourth_exists56`, which uses the compactness constant `Part48Hyper.fourth_moment 2`).
* `Clin64 = 2 + 64·5⁴`, `perpDir_linear_moment64`.
* `CK64 d = (2^d)² · Clin64`, `keyLemma64 : KeyLemma56 d (CK64 d)`.
* `CD64 d CK = d · Σ_{j=1}^d j⁴ · CK`, `propD64_of : PropD56 d (CD64 d CK)`.

The proofs are copies of the Part 56 proofs, with the witness stated. Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part64

open MeasureTheory BstLean.Part29 BstLean.Part56
open scoped ENNReal
open BstLean.Part41 (Mono)
open BstLean.Part62 (KCrit γ5 γ5_nonneg E4_le_γ5 fourth_moment_kappa)

lemma kcrit5_2 : KCrit 2 5 γ5 := by
  refine ⟨by norm_num, γ5_nonneg, fun c hc => E4_le_γ5 c ?_, ?_⟩
  · have := Finset.mem_Icc.mp hc; exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩
  · norm_num [Finset.sum_Icc_succ_top, γ5]

/-- `E P⁴ ≤ 5⁴ (E P²)²` for polynomials of degree `≤ 2`. -/
theorem fourth_moment_5_2 : ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ),
    P.totalDegree ≤ 2 →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        5 ^ 4 * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2 :=
  fourth_moment_kappa 2 5 γ5 kcrit5_2

private lemma pvecPoly_degree64 {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (pvecPoly56 v i).totalDegree ≤ 1 := by
  unfold pvecPoly56
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, add_zero]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro l hl
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp

private lemma qradPoly_degree64 {n : ℕ} (v : Fin n → ℝ) :
    (qradPoly56 v).totalDegree ≤ 2 := by
  unfold qradPoly56
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left 2 (pvecPoly_degree64 v i))

/-- The fourth central radial moment with the explicit constant `K₂ = 5⁴`. -/
theorem qrad_fourth64 : ∀ (n : ℕ) (v : Fin n → ℝ), UnitV v →
    (∫ g, (qrad56 v g - ((n : ℝ) - 1)) ^ 4 ∂stdGauss (Fin n)) ≤
      4 * (5 ^ 4 : ℝ) * ((n : ℝ) - 1) ^ 2 := by
  have hbound := fourth_moment_5_2
  intro n v hv
  let Q := qradPoly56 v - MvPolynomial.C ((n : ℝ) - 1)
  have hQ : Q.totalDegree ≤ 2 := by
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (qradPoly_degree64 v) (by rw [MvPolynomial.totalDegree_C]; omega))
  have h := hbound (Fin n) Q hQ
  simp only [Q, map_sub, MvPolynomial.eval_C, eval_qradPoly56] at h
  rw [qrad_variance56 v hv] at h
  convert h using 1
  ring
private lemma dot_bound64 {n : ℕ} (a w : Fin n → ℝ) (hw : ∑ i, w i ^ 2 ≤ 1) :
    dot56 a w ^ 2 ≤ ∑ i, a i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a w
  exact h.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hw
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))

private lemma dot_pvec64 {n : ℕ} (v a g : Fin n → ℝ) :
    dot56 a (pvec56 v g) = dot56 (pvec56 v a) g := by
  simp only [dot56, pvec56, mul_sub, sub_mul, Finset.sum_sub_distrib]
  have hL : (∑ x, a x * ((∑ l, v l * g l) * v x)) =
      (∑ l, v l * g l) * ∑ x, a x * v x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hR : (∑ x, (∑ l, v l * a l) * v x * g x) =
      (∑ l, v l * a l) * ∑ x, v x * g x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h (b : Fin n → ℝ) : (∑ i, b i * v i) = ∑ i, v i * b i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hL, hR, h]
  ring

private lemma linear_second64 {n : ℕ} (a : Fin n → ℝ) :
    (∫ g, dot56 a g ^ 2 ∂stdGauss (Fin n)) = ∑ i, a i ^ 2 := by
  have hm : GaussMoments n (stdGauss (Fin n)) := gaussMoments_std (D := n)
  have he (g : Fin n → ℝ) : dot56 a g ^ 2 =
      ∑ i, ∑ j, (a i * a j) * (g i * g j) := by
    simp only [dot56, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [integral_finsetSum _ fun i hi => integrable_finsetSum _
    fun j hj => (hm.int2 i j).const_mul _]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ fun j hj => (hm.int2 i j).const_mul _]
  simp only [integral_const_mul, hm.m2]
  simp [pow_two]

private lemma integrable_dot_pvec_sq64 {n : ℕ} (v a : Fin n → ℝ) :
    Integrable (fun g => dot56 a (pvec56 v g) ^ 2) (stdGauss (Fin n)) := by
  convert BstLean.Part48.gauss_poly_integrable ((∑ i,
    MvPolynomial.C (a i) * pvecPoly56 v i) ^ 2) using 1
  funext g
  simp only [map_pow, map_sum, map_mul, MvPolynomial.eval_C, eval_pvecPoly56, dot56]

private lemma integrable_dot_perpDir_sq64 {n : ℕ} (v a : Fin n → ℝ) :
    Integrable (fun g => dot56 a (perpDir v g) ^ 2) (stdGauss (Fin n)) := by
  have hm : Measurable (fun g => dot56 a (perpDir v g)) := by
    unfold dot56
    apply Finset.measurable_sum
    intro i hi
    exact ((measurable_pi_apply i).comp (measurable_perpDir56 v)).const_mul _
  apply Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (∑ i, a i ^ 2)
  filter_upwards [] with g
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact dot_bound64 a _ (perpDir_sq_le_one56 v g)

private lemma bad_radial_bound64 (q N : ℝ) (hN : 0 < N) (hq : q < N / 2) :
    1 ≤ 16 / N ^ 4 * (q - N) ^ 4 := by
  have hs : N / 2 ≤ |q - N| := by rw [abs_of_nonpos (by linarith)]; linarith
  have hp := pow_le_pow_left₀ (show 0 ≤ N / 2 by positivity) hs 4
  rw [pow_abs, div_pow, abs_of_nonneg (show 0 ≤ (q - N) ^ 4 by positivity)] at hp
  norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num] at hp
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hN 4)]
  nlinarith

private lemma dot_perpDir_dom64 {n : ℕ} (v a g : Fin n → ℝ) (N : ℝ) (hN : 0 < N) :
    dot56 a (perpDir v g) ^ 2 ≤ 2 / N * dot56 a (pvec56 v g) ^ 2 +
      ((∑ i, a i ^ 2) * (16 / N ^ 4)) * (qrad56 v g - N) ^ 4 := by
  have hq0 : 0 ≤ qrad56 v g := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he : dot56 a (perpDir v g) ^ 2 = dot56 a (pvec56 v g) ^ 2 / qrad56 v g := by
    have he' : dot56 a (perpDir v g) = (1 / Real.sqrt (qrad56 v g)) * dot56 a (pvec56 v g) := by
      change (∑ i, a i * ((1 / Real.sqrt (qrad56 v g)) * pvec56 v g i)) = _
      rw [dot56, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he', mul_pow, div_pow, Real.sq_sqrt hq0, one_pow]
    ring
  by_cases hq : N / 2 ≤ qrad56 v g
  · rw [he]
    have hb : dot56 a (pvec56 v g) ^ 2 / qrad56 v g ≤
        2 / N * dot56 a (pvec56 v g) ^ 2 := by
      rw [div_le_iff₀ (by linarith : 0 < qrad56 v g), div_mul_eq_mul_div,
        div_mul_eq_mul_div, le_div_iff₀ hN]
      nlinarith [mul_le_mul_of_nonneg_right hq (sq_nonneg (dot56 a (pvec56 v g)))]
    exact hb.trans (le_add_of_nonneg_right (by positivity))
  · have hb := mul_le_mul_of_nonneg_left
      (bad_radial_bound64 (qrad56 v g) N hN (lt_of_not_ge hq))
      (Finset.sum_nonneg (s := Finset.univ) (fun i hi => sq_nonneg (a i)))
    have hs := dot_bound64 a _ (perpDir_sq_le_one56 v g)
    simp only [mul_one] at hb
    refine hs.trans (hb.trans ?_)
    calc
      _ = ((∑ i, a i ^ 2) * (16 / N ^ 4)) * (qrad56 v g - N) ^ 4 := by ring
      _ ≤ _ := le_add_of_nonneg_left (by positivity)


/-- The explicit linear-functional constant `Clin64 = 2 + 64 · 5⁴`. -/
noncomputable def Clin64 : ℝ := 2 + 64 * 5 ^ 4

theorem perpDir_linear_moment64 :
    ∀ (n : ℕ), 2 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ a : Fin n → ℝ,
      (∫ g, dot56 a (perpDir v g) ^ 2 ∂stdGauss (Fin n)) ≤
        Clin64 / ((n : ℝ) - 1) * ∑ i, a i ^ 2 := by
  have hF := qrad_fourth64
  set K : ℝ := 5 ^ 4 with hKdef
  have hK : 0 < K := by norm_num
  unfold Clin64
  rw [← hKdef]
  intro n hn v hv a
  let N : ℝ := (n : ℝ) - 1
  let R : ℝ := ∑ i, a i ^ 2
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hN1 : 1 ≤ N := by
    dsimp [N]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hp : (∫ g, dot56 a (pvec56 v g) ^ 2 ∂stdGauss (Fin n)) ≤ R := by
    simp_rw [dot_pvec64]
    rw [linear_second64]
    change (∑ i, (a i - (∑ l, v l * a l) * v i) ^ 2) ≤ R
    rw [perpVec_sq56 v a hv]
    exact sub_le_self _ (sq_nonneg _)
  have hFv := hF n v hv
  change (∫ g, (qrad56 v g - N) ^ 4 ∂stdGauss (Fin n)) ≤ 4 * K * N ^ 2 at hFv
  have hc := integrable_qrad_center_pow56 v 4
  change Integrable (fun g => (qrad56 v g - N) ^ 4) (stdGauss (Fin n)) at hc
  have h := integral_mono (integrable_dot_perpDir_sq64 v a)
    (((integrable_dot_pvec_sq64 v a).const_mul (2 / N)).add (hc.const_mul (R * (16 / N ^ 4))))
    (fun g => dot_perpDir_dom64 v a g N hN)
  simp only [Pi.add_apply] at h
  rw [integral_add (f := fun g => 2 / N * dot56 a (pvec56 v g) ^ 2)
    (g := fun g => (R * (16 / N ^ 4)) * (qrad56 v g - N) ^ 4)
    ((integrable_dot_pvec_sq64 v a).const_mul _) (hc.const_mul _),
    integral_const_mul, integral_const_mul] at h
  have hb : (∫ g, dot56 a (perpDir v g) ^ 2 ∂stdGauss (Fin n)) ≤
      (2 / N + 64 * K / N ^ 2) * R := by
    refine h.trans ?_
    calc
      _ ≤ 2 / N * R + (R * (16 / N ^ 4)) * (4 * K * N ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hp (by positivity))
          (mul_le_mul_of_nonneg_left hFv (by positivity))
      _ = _ := by field_simp; ring
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ hR)
  change 2 / N + 64 * K / N ^ 2 ≤ (2 + 64 * K) / N
  rw [add_div]
  exact add_le_add le_rfl (div_le_div_of_nonneg_left (show 0 ≤ 64 * K by positivity)
    hN (by nlinarith : N ≤ N ^ 2))


lemma Clin64_pos : 0 < Clin64 := by unfold Clin64; norm_num

/-- The explicit Key Lemma constant `CK64 d = (2^d)² · Clin64`. -/
noncomputable def CK64 (d : ℕ) : ℝ := ((2 : ℝ) ^ d) ^ 2 * Clin64

lemma CK64_nonneg (d : ℕ) : 0 ≤ CK64 d := by unfold CK64; have := Clin64_pos; positivity

/-- **Key Lemma** (rank one) with the explicit constant. -/
theorem keyLemma64 (d : ℕ) : KeyLemma56 d (CK64 d) :=
  keyLemma56_from_linear d Clin64 Clin64_pos perpDir_linear_moment64

/-- The explicit Prop D constant `CD64 d CK = d · Σ_{j=1}^d j⁴ · CK`. -/
noncomputable def CD64 (d : ℕ) (CK : ℝ) : ℝ := (d : ℝ) * (∑ j ∈ Finset.Icc 1 d, (j : ℝ) ^ 4) * CK

/-- **Prop D** with the explicit constant `CD64 d CK`. -/
theorem propD64_of (d : ℕ) (hd : 1 ≤ d) (CK : ℝ) (hK : KeyLemma56 d CK) :
    0 ≤ CD64 d CK ∧ PropD56 d (CD64 d CK) := by
  classical
  refine ⟨?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun j _ => pow_nonneg (Nat.cast_nonneg _) _))
      (keyConstant_nonneg d hd CK hK)
  · intro n hn v hv t
    cases n with
    | zero => omega
    | succ k =>
      obtain ⟨b, hb⟩ := unit_basis_exists (k + 1) (by omega) v hv
      have hb0 : b 0 = WithLp.toLp 2 v := hb
      letI := axialMeasure_probability b v hb0 t
      have hm := lawRK_eq_polar_map b v hb0 t
      unfold deltaSq
      rw [hm, kernel_integral_map _ (polarState v) (measurable_polarState v)
        (fun x y => rhoR d v x y ^ 2) (measurable_rhoSq_PropD d v)]
      have h := mixed_correlation_integral_le d hd CK hK hn v hv (axialMeasure t v)
      simpa only [CD64, mul_div_assoc] using h

end BstLean.Part64
