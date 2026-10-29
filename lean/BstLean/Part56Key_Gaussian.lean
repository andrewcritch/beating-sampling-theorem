import BstLean.Part56Key_Projection
import BstLean.Part29Gauss
import BstLean.Part48Hyper

namespace BstLean.Part56

open MeasureTheory BstLean.Part29
open scoped ENNReal

def pvec56 {n : ℕ} (v g : Fin n → ℝ) : Fin n → ℝ :=
  fun i => g i - (∑ l, v l * g l) * v i

def qrad56 {n : ℕ} (v g : Fin n → ℝ) : ℝ := ∑ i, pvec56 v g i ^ 2

private lemma linear_second56 {n : ℕ} (c : Fin n → ℝ) :
    (∫ g, (∑ i, c i * g i) ^ 2 ∂stdGauss (Fin n)) = ∑ i, c i ^ 2 := by
  classical
  have hg : GaussMoments n (stdGauss (Fin n)) := gaussMoments_std (D := n)
  have he (g : Fin n → ℝ) : (∑ i, c i * g i) ^ 2 =
      ∑ i, ∑ l, (c i * c l) * (g i * g l) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro l hl
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun l _ => (hg.int2 i l).const_mul (c i * c l)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun l _ => (hg.int2 i l).const_mul (c i * c l))]
  simp_rw [integral_const_mul, hg.m2]
  simp [pow_two]

private lemma linear_fourth56 {n : ℕ} (c : Fin n → ℝ) :
    (∫ g, (∑ i, c i * g i) ^ 4 ∂stdGauss (Fin n)) = 3 * (∑ i, c i ^ 2) ^ 2 := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j => c i * c j
  have hb : B.IsSymm := by
    apply Matrix.ext
    intro i j
    dsimp [B, Matrix.transpose]
    ring
  have he (g : Fin n → ℝ) : qform B g = (∑ i, c i * g i) ^ 2 := by
    simp only [qform, B, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hg : GaussMoments n (stdGauss (Fin n)) := gaussMoments_std (D := n)
  have h := gauss_qform_sq (stdGauss (Fin n)) hg B hb
  simp_rw [he, ← pow_mul] at h
  norm_num only at h
  rw [h]
  dsimp [B]
  simp only [← pow_two, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

private def pmat56 {n : ℕ} (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (if i = j then 1 else 0) - v i * v j

private lemma pmat_trace56 {n : ℕ} (v : Fin n → ℝ) (hv : UnitV v) :
    (∑ i, pmat56 v i i) = (n : ℝ) - 1 := by
  simp only [pmat56, ite_true, ← pow_two, Finset.sum_sub_distrib]
  rw [hv]
  simp

private lemma pmat_frob56 {n : ℕ} (v : Fin n → ℝ) (hv : UnitV v) :
    (∑ i, ∑ j, pmat56 v i j ^ 2) = (n : ℝ) - 1 := by
  classical
  have hrow (i : Fin n) : (∑ j, pmat56 v i j ^ 2) = 1 - v i ^ 2 := by
    have h (j : Fin n) : pmat56 v i j ^ 2 =
        (if i = j then 1 else 0) - 2 * (if i = j then v i * v j else 0) +
          v i ^ 2 * v j ^ 2 := by
      unfold pmat56
      split_ifs <;> ring
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hv]
    simp
    ring
  simp_rw [hrow]
  rw [Finset.sum_sub_distrib, hv]
  simp

private lemma pvec_linear56 {n : ℕ} (v g : Fin n → ℝ) (i : Fin n) :
    pvec56 v g i = ∑ j, pmat56 v i j * g j := by
  classical
  simp only [pmat56, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  dsimp [pvec56]
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma qrad_qform56 {n : ℕ} (v g : Fin n → ℝ) (hv : UnitV v) :
    qrad56 v g = qform (pmat56 v) g := by
  classical
  rw [qrad56]
  change (∑ i, (g i - (∑ l, v l * g l) * v i) ^ 2) = _
  rw [perpVec_sq56 v g hv]
  simp only [qform, pmat56, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  · simp only [pow_two]
  · rw [pow_two]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring

theorem pvec_second56 {n : ℕ} (v : Fin n → ℝ) (hv : UnitV v) (i : Fin n) :
    (∫ g, pvec56 v g i ^ 2 ∂stdGauss (Fin n)) = 1 - v i ^ 2 := by
  simp_rw [pvec_linear56]
  rw [linear_second56]
  have hr (j : Fin n) : pmat56 v i j ^ 2 =
      (if i = j then 1 else 0) - 2 * (if i = j then v i * v j else 0) +
        v i ^ 2 * v j ^ 2 := by
    unfold pmat56
    split_ifs <;> ring
  simp_rw [hr]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hv]
  simp
  ring

theorem pvec_fourth56 {n : ℕ} (v : Fin n → ℝ) (hv : UnitV v) (i : Fin n) :
    (∫ g, pvec56 v g i ^ 4 ∂stdGauss (Fin n)) = 3 * (1 - v i ^ 2) ^ 2 := by
  simp_rw [pvec_linear56]
  rw [linear_fourth56]
  have hs := pvec_second56 v hv i
  simp_rw [pvec_linear56] at hs
  rw [linear_second56] at hs
  rw [hs]

noncomputable def pvecPoly56 {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.X i - (∑ l, MvPolynomial.C (v l) * MvPolynomial.X l) * MvPolynomial.C (v i)

noncomputable def qradPoly56 {n : ℕ} (v : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, pvecPoly56 v i ^ 2

theorem eval_pvecPoly56 {n : ℕ} (v g : Fin n → ℝ) (i : Fin n) :
    MvPolynomial.eval g (pvecPoly56 v i) = pvec56 v g i := by
  simp [pvecPoly56, pvec56]

theorem eval_qradPoly56 {n : ℕ} (v g : Fin n → ℝ) :
    MvPolynomial.eval g (qradPoly56 v) = qrad56 v g := by
  simp [qradPoly56, qrad56, eval_pvecPoly56]

theorem integrable_qrad_pow56 {n : ℕ} (v : Fin n → ℝ) (k : ℕ) :
    Integrable (fun g => qrad56 v g ^ k) (stdGauss (Fin n)) := by
  simpa only [map_pow, eval_qradPoly56] using
    BstLean.Part48.gauss_poly_integrable (qradPoly56 v ^ k)

theorem integrable_pvec_pow56 {n : ℕ} (v : Fin n → ℝ) (i : Fin n) (k : ℕ) :
    Integrable (fun g => pvec56 v g i ^ k) (stdGauss (Fin n)) := by
  simpa only [map_pow, eval_pvecPoly56] using
    BstLean.Part48.gauss_poly_integrable (pvecPoly56 v i ^ k)

theorem qrad_mean56 {n : ℕ} (v : Fin n → ℝ) (hv : UnitV v) :
    (∫ g, qrad56 v g ∂stdGauss (Fin n)) = (n : ℝ) - 1 := by
  unfold qrad56
  rw [integral_finsetSum _ fun i hi => integrable_pvec_pow56 v i 2]
  simp_rw [pvec_second56 v hv]
  rw [Finset.sum_sub_distrib, hv]
  simp

theorem qrad_second56 {n : ℕ} (v : Fin n → ℝ) (hv : UnitV v) :
    (∫ g, qrad56 v g ^ 2 ∂stdGauss (Fin n)) = ((n : ℝ) - 1) ^ 2 + 2 * ((n : ℝ) - 1) := by
  simp_rw [qrad_qform56 v _ hv]
  have hs : (pmat56 v).IsSymm := by
    apply Matrix.ext
    intro i j
    change pmat56 v j i = pmat56 v i j
    unfold pmat56
    simp only [eq_comm, mul_comm]
  have hg : GaussMoments n (stdGauss (Fin n)) := gaussMoments_std (D := n)
  rw [gauss_qform_sq _ hg _ hs,
    pmat_trace56 v hv, pmat_frob56 v hv]

theorem qrad_variance56 {n : ℕ} (v : Fin n → ℝ) (hv : UnitV v) :
    (∫ g, (qrad56 v g - ((n : ℝ) - 1)) ^ 2 ∂stdGauss (Fin n)) = 2 * ((n : ℝ) - 1) := by
  have hi := integrable_qrad_pow56 v 1
  simp only [pow_one] at hi
  have he (g : Fin n → ℝ) : (qrad56 v g - ((n : ℝ) - 1)) ^ 2 =
      qrad56 v g ^ 2 - (2 * ((n : ℝ) - 1)) * qrad56 v g + ((n : ℝ) - 1) ^ 2 := by ring
  simp_rw [he]
  rw [integral_add (f := fun g => qrad56 v g ^ 2 - (2 * ((n : ℝ) - 1)) * qrad56 v g)
      (g := fun _ => ((n : ℝ) - 1) ^ 2) ((integrable_qrad_pow56 v 2).sub
      (hi.const_mul (2 * ((n : ℝ) - 1)))) (integrable_const (((n : ℝ) - 1) ^ 2)),
    integral_sub (f := fun g => qrad56 v g ^ 2)
      (g := fun g => (2 * ((n : ℝ) - 1)) * qrad56 v g)
      (integrable_qrad_pow56 v 2) (hi.const_mul (2 * ((n : ℝ) - 1)))]
  rw [integral_const_mul, qrad_mean56 v hv, qrad_second56 v hv]
  simp only [integral_const, probReal_univ, one_smul]
  ring

private lemma pvecPoly_degree56 {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
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

private lemma qradPoly_degree56 {n : ℕ} (v : Fin n → ℝ) :
    (qradPoly56 v).totalDegree ≤ 2 := by
  unfold qradPoly56
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left 2 (pvecPoly_degree56 v i))

/-- A single dimension-free constant bounds the fourth central radial moment. -/
theorem qrad_fourth_exists56 : ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (v : Fin n → ℝ), UnitV v →
    (∫ g, (qrad56 v g - ((n : ℝ) - 1)) ^ 4 ∂stdGauss (Fin n)) ≤
      4 * K * ((n : ℝ) - 1) ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := BstLean.Part48.fourth_moment 2
  refine ⟨K, hK, ?_⟩
  intro n v hv
  let Q := qradPoly56 v - MvPolynomial.C ((n : ℝ) - 1)
  have hQ : Q.totalDegree ≤ 2 := by
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (qradPoly_degree56 v) (by rw [MvPolynomial.totalDegree_C]; omega))
  have h := hbound (Fin n) Q hQ
  simp only [Q, map_sub, MvPolynomial.eval_C, eval_qradPoly56] at h
  rw [qrad_variance56 v hv] at h
  convert h using 1
  ring

theorem integrable_qrad_center_pow56 {n : ℕ} (v : Fin n → ℝ) (k : ℕ) :
    Integrable (fun g => (qrad56 v g - ((n : ℝ) - 1)) ^ k) (stdGauss (Fin n)) := by
  convert BstLean.Part48.gauss_poly_integrable
    ((qradPoly56 v - MvPolynomial.C ((n : ℝ) - 1)) ^ k) using 1
  funext g
  simp only [map_pow, map_sub, MvPolynomial.eval_C, eval_qradPoly56]

end BstLean.Part56
