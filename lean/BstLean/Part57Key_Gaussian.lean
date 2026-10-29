import BstLean.Part57Key_Projection
import BstLean.Part29Gauss

/-! Gaussian second moments and radial variance bounds for frame complements. -/

namespace BstLean.Part57.KeyProof
open MeasureTheory BstLean.Part29 BstLean.Part56
variable {n r : ℕ}

lemma linear_second (c : Fin n → ℝ) :
    (∫ g, (∑ i, c i * g i) ^ 2 ∂stdGauss (Fin n)) = ∑ i, c i ^ 2 := by
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

noncomputable def ppoly (V : Fin r → Fin n → ℝ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.X i - ∑ a, (∑ l, MvPolynomial.C (V a l) * MvPolynomial.X l) * MvPolynomial.C (V a i)

noncomputable def qpoly (V : Fin r → Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, ppoly V i ^ 2

lemma eval_ppoly (V : Fin r → Fin n → ℝ) (g : Fin n → ℝ) (i : Fin n) :
    MvPolynomial.eval g (ppoly V i) = pvec V g i := by
  simp [ppoly, pvec, coordY]

lemma eval_qpoly (V : Fin r → Fin n → ℝ) (g : Fin n → ℝ) :
    MvPolynomial.eval g (qpoly V) = rhoSq V g := by
  simp [qpoly, rhoSq, eval_ppoly, pvec]

lemma int_rad_pow (V : Fin r → Fin n → ℝ) (k : ℕ) :
    Integrable (fun g => rhoSq V g ^ k) (stdGauss (Fin n)) := by
  simpa only [map_pow, eval_qpoly] using BstLean.Part48.gauss_poly_integrable (qpoly V ^ k)

lemma int_rad_center (V : Fin r → Fin n → ℝ) (k : ℕ) :
    Integrable (fun g => (rhoSq V g - ((n : ℝ) - r)) ^ k) (stdGauss (Fin n)) := by
  convert BstLean.Part48.gauss_poly_integrable
    ((qpoly V - MvPolynomial.C ((n : ℝ) - r)) ^ k) using 1
  funext g
  simp only [map_pow, map_sub, MvPolynomial.eval_C, eval_qpoly]

def pmat (V : Fin r → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (if i = j then 1 else 0) - ∑ a, V a i * V a j

lemma pmat_symm (V : Fin r → Fin n → ℝ) : (pmat V).IsSymm := by
  apply Matrix.ext
  intro i j
  simp only [pmat, Matrix.transpose_apply, eq_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma pmat_trace (V : Fin r → Fin n → ℝ) (hV : OrthoF V) :
    ∑ i, pmat V i i = (n : ℝ) - r := by
  simp only [pmat, ite_true, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  have he (a : Fin r) : ∑ i, V a i * V a i = 1 := by simpa using hV a a
  simp only [he]
  simp

lemma pmat_frob (V : Fin r → Fin n → ℝ) (hV : OrthoF V) :
    (∑ i, ∑ j, pmat V i j ^ 2) ≤ (n : ℝ) := by
  classical
  have hr (i : Fin n) : (∑ j, pmat V i j ^ 2) ≤ 1 := by
    let e : Fin n → ℝ := fun j => if i = j then 1 else 0
    have he : pvec V e = fun j => pmat V i j := by
      ext j
      simp only [pvec, coordY, e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, pmat]
    have hc := pvec_contract V hV e
    rw [he] at hc
    simpa [e] using hc
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hr i
    _ = _ := by simp

lemma rad_qform (V : Fin r → Fin n → ℝ) (hV : OrthoF V) (g : Fin n → ℝ) :
    rhoSq V g = qform (pmat V) g := by
  classical
  rw [rho_eq V hV]
  simp only [qform, pmat, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  · simp only [pow_two]
  · simp only [coordY, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro a ha
    ring

lemma rad_mean (V : Fin r → Fin n → ℝ) (hV : OrthoF V) :
    (∫ g, rhoSq V g ∂stdGauss (Fin n)) = (n : ℝ) - r := by
  have hi : ∀ i j : Fin n, Integrable (fun g => g i * g j) (stdGauss (Fin n)) :=
    (gaussMoments_std (D := n)).int2
  simp_rw [rad_qform V hV]
  unfold qform
  have he (i j : Fin n) (g : Fin n → ℝ) : pmat V i j * g i * g j = pmat V i j * (g i * g j) := by ring
  simp_rw [he]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hi i j).const_mul (pmat V i j)]
  have hg : GaussMoments n (stdGauss (Fin n)) := gaussMoments_std (D := n)
  calc
    _ = ∑ i, pmat V i i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ fun j _ => (hg.int2 i j).const_mul (pmat V i j)]
      simp only [integral_const_mul, hg.m2]
      simp
    _ = _ := pmat_trace V hV

lemma rad_second (V : Fin r → Fin n → ℝ) (hV : OrthoF V) :
    (∫ g, rhoSq V g ^ 2 ∂stdGauss (Fin n)) ≤ ((n : ℝ) - r) ^ 2 + 2 * n := by
  simp_rw [rad_qform V hV]
  have hg : GaussMoments n (stdGauss (Fin n)) := gaussMoments_std (D := n)
  rw [gauss_qform_sq _ hg _ (pmat_symm V), pmat_trace V hV]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (pmat_frob V hV) (show (0 : ℝ) ≤ 2 by norm_num))

lemma rad_variance (V : Fin r → Fin n → ℝ) (hV : OrthoF V) :
    (∫ g, (rhoSq V g - ((n : ℝ) - r)) ^ 2 ∂stdGauss (Fin n)) ≤ 2 * n := by
  have hi := int_rad_pow V 1
  simp only [pow_one] at hi
  let N : ℝ := (n : ℝ) - r
  have he (g : Fin n → ℝ) : (rhoSq V g - N) ^ 2 = rhoSq V g ^ 2 - (2 * N) * rhoSq V g + N ^ 2 := by ring
  change (∫ g, (rhoSq V g - N) ^ 2 ∂stdGauss (Fin n)) ≤ 2 * n
  simp_rw [he]
  rw [integral_add (f := fun g => rhoSq V g ^ 2 - (2 * N) * rhoSq V g)
      (g := fun _ => N ^ 2) ((int_rad_pow V 2).sub (hi.const_mul (2 * N))) (integrable_const (N ^ 2)),
    integral_sub (f := fun g => rhoSq V g ^ 2) (g := fun g => (2 * N) * rhoSq V g)
      (int_rad_pow V 2) (hi.const_mul (2 * N)), integral_const_mul, rad_mean V hV]
  simp only [integral_const, probReal_univ, one_smul]
  have hs := rad_second V hV
  dsimp [N]
  linarith

lemma dot_second (V : Fin r → Fin n → ℝ) (hV : OrthoF V) (a : Fin n → ℝ) :
    (∫ g, dot56 a (pvec V g) ^ 2 ∂stdGauss (Fin n)) ≤ ∑ i, a i ^ 2 := by
  simp_rw [dot_pvec]
  change (∫ g, (∑ i, pvec V a i * g i) ^ 2 ∂stdGauss (Fin n)) ≤ _
  rw [linear_second]
  exact pvec_contract V hV a

lemma int_dot_sq (V : Fin r → Fin n → ℝ) (a : Fin n → ℝ) :
    Integrable (fun g => dot56 a (pvec V g) ^ 2) (stdGauss (Fin n)) := by
  convert BstLean.Part48.gauss_poly_integrable ((∑ i, MvPolynomial.C (a i) * ppoly V i) ^ 2) using 1
  funext g
  simp only [map_pow, map_sum, map_mul, MvPolynomial.eval_C, eval_ppoly, dot56]

end BstLean.Part57.KeyProof
