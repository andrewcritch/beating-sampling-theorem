import BstLean.Part90Var
import BstLean.Part78Deg2
import BstLean.Part78Wick

/-!
# Part 90: the fourth moment of the gradient fluctuation (`GradL4`)

`G_x − Ā = (A_x − Ā) + 2 H_x r + 3 (T[r,r] − k b)`, Minkowski in `L⁴` in the weighted convexity
form `(f+g+h)⁴ ≤ f⁴/λ₁³ + g⁴/λ₂³ + h⁴/λ₃³`, and the Gaussian fourth-moment bounds with the constants
`3` (degree one) and `35/2` (degree two).
-/

namespace BstLean.Part90

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss)
open BstLean.Part40 (SphLaw)
open BstLean.Part48 (gauss_poly_integrable)
open BstLean.Part78 (nsq frobH trH zv PP gpi78 poly_cs78)
open BstLean.Part80 (kA sph_int PP_int_x PP_int_prod)
open BstLean.Part82 (T3 SymT frobT trT aU3 HU3)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ### Real-variable lemmas -/

lemma jensen4 (f g h l1 l2 l3 : ℝ) (hf : 0 ≤ f) (hg : 0 ≤ g) (hh : 0 ≤ h) (h1 : 0 < l1)
    (h2 : 0 < l2) (h3 : 0 < l3) (hs : l1 + l2 + l3 = 1) :
    (f + g + h) ^ 4 ≤ f ^ 4 / l1 ^ 3 + g ^ 4 / l2 ^ 3 + h ^ 4 / l3 ^ 3 := by
  have key := Real.pow_arith_mean_le_arith_mean_pow (Finset.univ : Finset (Fin 3)) ![l1, l2, l3]
    ![f / l1, g / l2, h / l3]
    (by intro i _; fin_cases i <;> simp <;> positivity)
    (by simp [Fin.sum_univ_three, hs])
    (by intro i _; fin_cases i <;> simp <;> positivity) 4
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at key
  have e1 : l1 * (f / l1) = f := by field_simp
  have e2 : l2 * (g / l2) = g := by field_simp
  have e3 : l3 * (h / l3) = h := by field_simp
  have e4 : l1 * (f / l1) ^ 4 = f ^ 4 / l1 ^ 3 := by field_simp
  have e5 : l2 * (g / l2) ^ 4 = g ^ 4 / l2 ^ 3 := by field_simp
  have e6 : l3 * (h / l3) ^ 4 = h ^ 4 / l3 ^ 3 := by field_simp
  rw [e1, e2, e3, e4, e5, e6] at key
  exact key

lemma lim4 (X S : ℝ) (h : ∀ ε : ℝ, 0 < ε → X ≤ (S + 3 * ε) ^ 4) : X ≤ S ^ 4 := by
  have hc : Continuous fun ε : ℝ => (S + 3 * ε) ^ 4 := by fun_prop
  have ht : Filter.Tendsto (fun ε : ℝ => (S + 3 * ε) ^ 4) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (S ^ 4)) := by
    have := hc.tendsto 0
    simp only [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => h ε hε)

/-- Minkowski in `L⁴` for three terms, in the weighted form. -/
lemma comb3 (X P Q R A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hP : P ≤ A ^ 4)
    (hQ : Q ≤ B ^ 4) (hR : R ≤ C ^ 4)
    (h : ∀ l1 l2 l3 : ℝ, 0 < l1 → 0 < l2 → 0 < l3 → l1 + l2 + l3 = 1 →
      X ≤ P / l1 ^ 3 + Q / l2 ^ 3 + R / l3 ^ 3) : X ≤ (A + B + C) ^ 4 := by
  refine lim4 _ _ fun ε hε => ?_
  have hA' : 0 < A + ε := by linarith
  have hB' : 0 < B + ε := by linarith
  have hC' : 0 < C + ε := by linarith
  have hS : 0 < (A + ε) + (B + ε) + (C + ε) := by linarith
  set S := (A + ε) + (B + ε) + (C + ε) with hSd
  have hh := h ((A + ε) / S) ((B + ε) / S) ((C + ε) / S) (by positivity) (by positivity)
    (by positivity) (by rw [← add_div, ← add_div]; exact div_self hS.ne')
  have b1 : P / ((A + ε) / S) ^ 3 ≤ (A + ε) * S ^ 3 := by
    have : P ≤ (A + ε) ^ 4 := hP.trans (pow_le_pow_left₀ hA (by linarith) 4)
    have := div_le_div_of_nonneg_right this (by positivity : (0:ℝ) ≤ ((A + ε) / S) ^ 3)
    refine this.trans (le_of_eq ?_); field_simp
  have b2 : Q / ((B + ε) / S) ^ 3 ≤ (B + ε) * S ^ 3 := by
    have : Q ≤ (B + ε) ^ 4 := hQ.trans (pow_le_pow_left₀ hB (by linarith) 4)
    have := div_le_div_of_nonneg_right this (by positivity : (0:ℝ) ≤ ((B + ε) / S) ^ 3)
    refine this.trans (le_of_eq ?_); field_simp
  have b3 : R / ((C + ε) / S) ^ 3 ≤ (C + ε) * S ^ 3 := by
    have : R ≤ (C + ε) ^ 4 := hR.trans (pow_le_pow_left₀ hC (by linarith) 4)
    have := div_le_div_of_nonneg_right this (by positivity : (0:ℝ) ≤ ((C + ε) / S) ^ 3)
    refine this.trans (le_of_eq ?_); field_simp
  have e : (A + B + C + 3 * ε) ^ 4 = (A + ε) * S ^ 3 + (B + ε) * S ^ 3 + (C + ε) * S ^ 3 := by
    rw [hSd]; ring
  rw [e]; linarith

/-! ### The triangle inequality -/

section tri
variable {ι : Type*} [Fintype ι]

lemma tri2 (a b : ι → ℝ) : Real.sqrt (∑ i, (a i + b i) ^ 2) ≤
    Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2) := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have ea : Real.sqrt (∑ i, a i ^ 2) ^ 2 = ∑ i, a i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (a i))
  have eb : Real.sqrt (∑ i, b i ^ 2) ^ 2 = ∑ i, b i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (b i))
  have e : ∑ i, (a i + b i) ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ i, a i * b i + ∑ i, b i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  nlinarith

lemma tri4 (a b c : ι → ℝ) (l1 l2 l3 : ℝ) (h1 : 0 < l1) (h2 : 0 < l2) (h3 : 0 < l3)
    (hs : l1 + l2 + l3 = 1) :
    (∑ i, (a i + b i + c i) ^ 2) ^ 2 ≤ (∑ i, a i ^ 2) ^ 2 / l1 ^ 3 + (∑ i, b i ^ 2) ^ 2 / l2 ^ 3 +
      (∑ i, c i ^ 2) ^ 2 / l3 ^ 3 := by
  have t1 := tri2 (fun i => a i + b i) c
  have t2 := tri2 a b
  have n0 : 0 ≤ ∑ i, (a i + b i + c i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have na : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have nb : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have nc : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have j := jensen4 _ _ _ l1 l2 l3 (Real.sqrt_nonneg (∑ i, a i ^ 2))
    (Real.sqrt_nonneg (∑ i, b i ^ 2)) (Real.sqrt_nonneg (∑ i, c i ^ 2)) h1 h2 h3 hs
  have p4 (y : ℝ) (hy : 0 ≤ y) : Real.sqrt y ^ 4 = y ^ 2 := by
    have : Real.sqrt y ^ 4 = (Real.sqrt y ^ 2) ^ 2 := by ring
    rw [this, Real.sq_sqrt hy]
  rw [p4 _ na, p4 _ nb, p4 _ nc] at j
  rw [← p4 _ n0]
  exact (pow_le_pow_left₀ (Real.sqrt_nonneg _) (by linarith) 4).trans j

end tri

/-! ### The fourth moment of a sum of squares of Gaussian polynomials -/

lemma sumsq4 {κ : Type} [Fintype κ] {n : ℕ} (P : Fin n → MvPolynomial κ ℝ) (c : ℝ)
    (m : Fin n → ℝ) (hc : 0 ≤ c) (hm : ∀ i, 0 ≤ m i)
    (h4 : ∀ i, ∫ z, (eval z (P i)) ^ 4 ∂stdGauss κ ≤ c * m i ^ 2) :
    ∫ z, (∑ i, (eval z (P i)) ^ 2) ^ 2 ∂stdGauss κ ≤ c * (∑ i, m i) ^ 2 := by
  have hpair (i j : Fin n) :
      ∫ z, (eval z (P i)) ^ 2 * (eval z (P j)) ^ 2 ∂stdGauss κ ≤ c * m i * m j := by
    have cs := poly_cs78 (P i ^ 2) (P j ^ 2)
    simp only [map_pow] at cs
    have e (y : ℝ) : (y ^ 2) ^ 2 = y ^ 4 := by ring
    simp only [e] at cs
    have hi := h4 i
    have hj := h4 j
    have n4i : 0 ≤ ∫ z, (eval z (P i)) ^ 4 ∂stdGauss κ :=
      integral_nonneg fun z => by positivity
    have n4j : 0 ≤ ∫ z, (eval z (P j)) ^ 4 ∂stdGauss κ :=
      integral_nonneg fun z => by positivity
    have hb : 0 ≤ c * m i * m j := mul_nonneg (mul_nonneg hc (hm i)) (hm j)
    have hsq : (∫ z, (eval z (P i)) ^ 2 * (eval z (P j)) ^ 2 ∂stdGauss κ) ^ 2 ≤
        (c * m i * m j) ^ 2 := by
      refine cs.trans ?_
      have := mul_le_mul hi hj n4j (n4i.trans hi)
      refine this.trans (le_of_eq ?_); ring
    exact (abs_le_of_sq_le_sq' hsq hb).2
  have e : (fun z : κ → ℝ => (∑ i, (eval z (P i)) ^ 2) ^ 2) = fun z =>
      ∑ i, ∑ j, (eval z (P i)) ^ 2 * (eval z (P j)) ^ 2 := by
    funext z; rw [pow_two, Finset.sum_mul_sum]
  have ii (i j : Fin n) : Integrable (fun z : κ → ℝ => (eval z (P i)) ^ 2 * (eval z (P j)) ^ 2)
      (stdGauss κ) := by
    have := gauss_poly_integrable (P i ^ 2 * P j ^ 2)
    simpa only [map_mul, map_pow] using this
  rw [e, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ii i j]
  simp_rw [integral_finsetSum _ fun j _ => ii _ j]
  calc ∑ i, ∑ j, ∫ z, (eval z (P i)) ^ 2 * (eval z (P j)) ^ 2 ∂stdGauss κ
      ≤ ∑ i, ∑ j, c * m i * m j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = c * (∑ i, m i) ^ 2 := by
        rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring

/-! ### The algebra of the gradient -/

lemma grad_alg {n : ℕ} (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (hT : SymT T)
    (u r : Fin n → ℝ) (i : Fin n) (k Ab : ℝ) :
    aU3 ℓ H T (fun l => u l + r l) i - Ab =
      (aU3 ℓ H T u i + 3 * k * trT T i - Ab) +
        (2 * ∑ j, HU3 H T u i j * r j +
          3 * (∑ j, ∑ l, T i j l * r j * r l - k * trT T i)) := by
  have sw : ∑ j, ∑ l, T i j l * u j * r l = ∑ j, ∑ l, T i j l * r j * u l := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [(hT i b a).2]; ring
  have e1 : ∑ j, H i j * (u j + r j) = ∑ j, H i j * u j + ∑ j, H i j * r j := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, ∑ l, T i j l * (u j + r j) * (u l + r l) =
      ∑ j, ∑ l, T i j l * u j * u l + ∑ j, ∑ l, T i j l * u j * r l +
        ∑ j, ∑ l, T i j l * r j * u l + ∑ j, ∑ l, T i j l * r j * r l := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have e3 : ∑ j, HU3 H T u i j * r j =
      ∑ j, H i j * r j + 3 * ∑ j, ∑ l, T i j l * r j * u l := by
    have hj : ∀ j, HU3 H T u i j * r j = H i j * r j + 3 * ∑ l, T i j l * r j * u l := by
      intro j
      simp only [HU3, Matrix.of_apply]
      rw [add_mul, mul_assoc, Finset.sum_mul]
      congr 2
      exact Finset.sum_congr rfl fun l _ => by ring
    simp_rw [hj]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  simp only [aU3]
  rw [e1, e2, e3, sw]
  ring

/-! ### The polynomials -/

variable {n : ℕ} {J : Type} [Fintype J] (D : DatC n J)

lemma cont_Hx (i j : Fin n) : Continuous fun x => HxC D.H D.T D.mu x i j := by
  simp only [HxC, HU3, Matrix.of_apply]
  exact continuous_const.add (continuous_const.mul
    (continuous_finsetSum _ fun k _ => continuous_const.mul (D.cmu k)))

lemma cont_kA : Continuous (kA D.ψ) := by
  unfold kA
  exact continuous_finsetSum _ fun q _ => (D.cψ q).pow 2

/-- `(H_x r)_i` as a polynomial in `W`. -/
noncomputable def UpC (i : Fin n) (x : Fin n → ℝ) : MvPolynomial (J × Fin n) ℝ :=
  ∑ j, C (HxC D.H D.T D.mu x i j) * ZpC D x j

/-- `T_i[r,r]` as a polynomial in `W`. -/
noncomputable def QqC (i : Fin n) (x : Fin n → ℝ) : MvPolynomial (J × Fin n) ℝ :=
  ∑ j, ∑ l, C (D.T i j l) * ZpC D x j * ZpC D x l

/-- `T_i[r,r] − k b_i` as a polynomial in `W`. -/
noncomputable def VpC (i : Fin n) (x : Fin n → ℝ) : MvPolynomial (J × Fin n) ℝ :=
  QqC D i x - C (kA D.ψ x * trT D.T i)

lemma PP_UpC (i : Fin n) : PP 1 (UpC D i) := by
  unfold UpC
  exact PP.sum _ fun j _ =>
    ((PP.coef (ι := J × Fin n) (cont_Hx D i j)).mul (PP_ZpC D j)).mono (by norm_num)

lemma PP_QqC (i : Fin n) : PP 2 (QqC D i) := by
  unfold QqC
  exact PP.sum _ fun j _ => PP.sum _ fun l _ =>
    (((PP_CcC (D.T i j l)).mul (PP_ZpC D j)).mul (PP_ZpC D l)).mono (by norm_num)

lemma PP_VpC (i : Fin n) : PP 2 (VpC D i) := by
  unfold VpC
  exact (PP_QqC D i).sub ((PP.coef (ι := J × Fin n)
    ((cont_kA D).mul continuous_const)).mono (by norm_num))

lemma eval_UpC (i : Fin n) (x : Fin n → ℝ) (W : J × Fin n → ℝ) :
    eval W (UpC D i x) = ∑ j, HxC D.H D.T D.mu x i j * zv W (D.ψ x) j := by
  simp only [UpC, map_sum, map_mul, eval_C, eval_ZpC]

lemma eval_QqC (i : Fin n) (x : Fin n → ℝ) (W : J × Fin n → ℝ) :
    eval W (QqC D i x) = ∑ j, ∑ l, D.T i j l * zv W (D.ψ x) j * zv W (D.ψ x) l := by
  simp only [QqC, map_sum, map_mul, eval_C, eval_ZpC]

lemma eval_VpC (i : Fin n) (x : Fin n → ℝ) (W : J × Fin n → ℝ) :
    eval W (VpC D i x) = ∑ j, ∑ l, D.T i j l * zv W (D.ψ x) j * zv W (D.ψ x) l -
      kA D.ψ x * trT D.T i := by
  simp only [VpC, map_sub, eval_C, eval_QqC]

/-- The decomposition of the gradient fluctuation. -/
lemma G_decomp (hT : SymT D.T) (Abar : Fin n → ℝ) (i : Fin n) (x : Fin n → ℝ)
    (W : J × Fin n → ℝ) :
    GvC D i x W - Abar i = (AxC D.ℓ D.H D.T D.mu D.ψ x i - Abar i) +
      2 * eval W (UpC D i x) + 3 * eval W (VpC D i x) := by
  rw [eval_UpC, eval_VpC]
  unfold GvC AxC HxC
  rw [grad_alg D.ℓ D.H D.T hT (D.mu x) (zv W (D.ψ x)) i (kA D.ψ x) (Abar i)]
  ring

/-! ### Moments in `W` at a fixed `x` -/

lemma U_lin (i : Fin n) (x : Fin n → ℝ) (W : J × Fin n → ℝ) :
    eval W (UpC D i x) =
      ∑ β : J × Fin n, (HxC D.H D.T D.mu x i β.2 * D.ψ x β.1) * W β := by
  rw [eval_UpC, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold zv
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

lemma U_m4 (i : Fin n) (x : Fin n → ℝ) :
    ∫ W, (eval W (UpC D i x)) ^ 4 ∂stdGauss (J × Fin n) ≤
      3 * (kA D.ψ x * ∑ j, HxC D.H D.T D.mu x i j ^ 2) ^ 2 := by
  have h4 := BstLean.Part78.affFourth3 (J × Fin n) 0
    (fun β : J × Fin n => HxC D.H D.T D.mu x i β.2 * D.ψ x β.1)
  have h2 := (BstLean.Part78.gaussLin (J × Fin n)
    (fun β : J × Fin n => HxC D.H D.T D.mu x i β.2 * D.ψ x β.1)
    (fun β : J × Fin n => HxC D.H D.T D.mu x i β.2 * D.ψ x β.1)).2
  simp only [zero_add, ← U_lin, ← pow_two] at h4 h2
  rw [h2] at h4
  refine h4.trans (le_of_eq ?_)
  congr 2
  rw [Fintype.sum_prod_type, kA, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun j _ => by ring

/-- `Σ_{jl} T_{ijl}²`. -/
def tF (T : T3 n) (i : Fin n) : ℝ := ∑ j, ∑ l, T i j l ^ 2

lemma V_m2 (hT : SymT D.T) (i : Fin n) (x : Fin n → ℝ) :
    ∫ W, (eval W (VpC D i x)) ^ 2 ∂stdGauss (J × Fin n) = 2 * kA D.ψ x ^ 2 * tF D.T i := by
  set Ti : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun j l => D.T i j l with hTi
  have hsym : Ti.IsSymm := by
    ext j l
    simp only [hTi, Matrix.transpose_apply, Matrix.of_apply]
    exact ((hT i j l).2).symm
  obtain ⟨w1, w2⟩ := BstLean.Part78.wickTwoPoint J n 0 Ti hsym (D.ψ x) (D.ψ x)
  have hPhi (W : J × Fin n → ℝ) : BstLean.Part78.Phi 0 Ti W (D.ψ x) = eval W (QqC D i x) := by
    rw [eval_QqC]
    simp [BstLean.Part78.Phi, hTi]
  simp only [hPhi] at w1 w2
  have hk : ∑ q, D.ψ x q * D.ψ x q = kA D.ψ x :=
    Finset.sum_congr rfl fun q _ => by ring
  have hk' : ∑ q, D.ψ x q ^ 2 = kA D.ψ x := rfl
  rw [hk, hk'] at w2
  rw [hk'] at w1
  have htr : trH Ti = trT D.T i := rfl
  have hfr : frobH Ti = tF D.T i := rfl
  have hn0 : nsq (0 : Fin n → ℝ) = 0 := by simp [nsq]
  rw [htr] at w1
  rw [htr, hfr, hn0] at w2
  set c := kA D.ψ x * trT D.T i with hc
  have e : (fun W : J × Fin n → ℝ => (eval W (VpC D i x)) ^ 2) = fun W =>
      eval W (QqC D i x) * eval W (QqC D i x) - (2 * c) * eval W (QqC D i x) + c ^ 2 := by
    funext W; simp only [VpC, map_sub, eval_C]; ring
  have i1 : Integrable (fun W : J × Fin n → ℝ => eval W (QqC D i x) * eval W (QqC D i x))
      (stdGauss (J × Fin n)) := by
    have := gpi78 (QqC D i x) 2
    simpa only [pow_two] using this
  have i2 : Integrable (fun W : J × Fin n → ℝ => (2 * c) * eval W (QqC D i x))
      (stdGauss (J × Fin n)) := (gauss_poly_integrable _).const_mul _
  have e1 : ∫ W, (eval W (QqC D i x) * eval W (QqC D i x) - (2 * c) * eval W (QqC D i x) +
      c ^ 2) ∂stdGauss (J × Fin n) =
      ∫ W, (eval W (QqC D i x) * eval W (QqC D i x) - (2 * c) * eval W (QqC D i x))
        ∂stdGauss (J × Fin n) + ∫ _W, c ^ 2 ∂stdGauss (J × Fin n) :=
    integral_add (i1.sub i2) (integrable_const _)
  have e2 : ∫ W, (eval W (QqC D i x) * eval W (QqC D i x) - (2 * c) * eval W (QqC D i x))
        ∂stdGauss (J × Fin n) =
      ∫ W, eval W (QqC D i x) * eval W (QqC D i x) ∂stdGauss (J × Fin n) -
        ∫ W, (2 * c) * eval W (QqC D i x) ∂stdGauss (J × Fin n) := integral_sub i1 i2
  rw [e, e1, e2, integral_const_mul, integral_const, w1, w2]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [hc]; ring

lemma tF_nonneg (T : T3 n) (i : Fin n) : 0 ≤ tF T i :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => sq_nonneg _

lemma V_m4 (hT : SymT D.T) (i : Fin n) (x : Fin n → ℝ) :
    ∫ W, (eval W (VpC D i x)) ^ 4 ∂stdGauss (J × Fin n) ≤
      35 / 2 * (2 * kA D.ψ x ^ 2 * tF D.T i) ^ 2 := by
  have h := BstLean.Part78.deg2Fourth (J × Fin n) (VpC D i x) ((PP_VpC D i).deg x)
  rwa [V_m2 D hT] at h

lemma kA_nonneg (x : Fin n → ℝ) : 0 ≤ kA D.ψ x := Finset.sum_nonneg fun q _ => sq_nonneg _

lemma U_x (x : Fin n → ℝ) :
    ∫ W, (∑ i, (eval W (UpC D i x)) ^ 2) ^ 2 ∂stdGauss (J × Fin n) ≤
      3 * (kA D.ψ x * frobH (HxC D.H D.T D.mu x)) ^ 2 := by
  have h := sumsq4 (fun i => UpC D i x) 3
    (fun i => kA D.ψ x * ∑ j, HxC D.H D.T D.mu x i j ^ 2) (by norm_num)
    (fun i => mul_nonneg (kA_nonneg D x) (Finset.sum_nonneg fun j _ => sq_nonneg _))
    (fun i => U_m4 D i x)
  rw [← Finset.mul_sum] at h
  exact h

lemma V_x (hT : SymT D.T) (x : Fin n → ℝ) :
    ∫ W, (∑ i, (eval W (VpC D i x)) ^ 2) ^ 2 ∂stdGauss (J × Fin n) ≤
      35 / 2 * (2 * kA D.ψ x ^ 2 * frobT D.T) ^ 2 := by
  have h := sumsq4 (fun i => VpC D i x) (35 / 2)
    (fun i => 2 * kA D.ψ x ^ 2 * tF D.T i) (by norm_num)
    (fun i => mul_nonneg (by positivity) (tF_nonneg D.T i))
    (fun i => V_m4 D hT i x)
  rw [← Finset.mul_sum] at h
  exact h

/-! ### Integration helpers -/

lemma int3 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (R A U V : Ω → ℝ) (c1 c2 c3 : ℝ)
    (hR : Integrable R μ) (hA : Integrable A μ) (hU : Integrable U μ) (hV : Integrable V μ)
    (h : ∀ w, R w ≤ c1 * A w + c2 * U w + c3 * V w) :
    ∫ w, R w ∂μ ≤ c1 * ∫ w, A w ∂μ + c2 * ∫ w, U w ∂μ + c3 * ∫ w, V w ∂μ := by
  have j1 : Integrable (fun w => c1 * A w) μ := hA.const_mul _
  have j2 : Integrable (fun w => c2 * U w) μ := hU.const_mul _
  have j3 : Integrable (fun w => c3 * V w) μ := hV.const_mul _
  have j12 : Integrable (fun w => c1 * A w + c2 * U w) μ := j1.add j2
  have j123 : Integrable (fun w => c1 * A w + c2 * U w + c3 * V w) μ := j12.add j3
  have e : c1 * ∫ w, A w ∂μ + c2 * ∫ w, U w ∂μ + c3 * ∫ w, V w ∂μ =
      ∫ w, (c1 * A w + c2 * U w + c3 * V w) ∂μ := by
    rw [integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
      integral_const_mul]
  rw [e]
  exact integral_mono hR j123 h

lemma frobH_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frobH M :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

lemma frob_tri {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) (l1 l2 l3 : ℝ) (h1 : 0 < l1)
    (h2 : 0 < l2) (h3 : 0 < l3) (hs : l1 + l2 + l3 = 1) :
    frobH M ^ 2 ≤ frobH N ^ 2 / l1 ^ 3 + frobH (M - N) ^ 2 / l2 ^ 3 := by
  have e (A : Matrix (Fin n) (Fin n) ℝ) : frobH A = ∑ p : Fin n × Fin n, A p.1 p.2 ^ 2 := by
    unfold frobH; rw [Fintype.sum_prod_type]
  have t := tri4 (ι := Fin n × Fin n) (fun p => N p.1 p.2) (fun p => (M - N) p.1 p.2)
    (fun _ => 0) l1 l2 l3 h1 h2 h3 hs
  have e0 : ∑ p : Fin n × Fin n, (N p.1 p.2 + (M - N) p.1 p.2 + 0) ^ 2 = frobH M := by
    rw [e M]; exact Finset.sum_congr rfl fun p _ => by simp
  rw [e0, ← e N, ← e (M - N)] at t
  simpa using t

/-! ### The theorem -/

theorem gradL4_D (hT : SymT D.T) (Abar : Fin n → ℝ) (Hbar : Matrix (Fin n) (Fin n) ℝ)
    (K t rt cH cT dA dH hb tt : ℝ) (hK : 0 ≤ K) (hrt : 0 ≤ rt) (ht : rt ^ 2 = t) (hcH : 0 ≤ cH)
    (hcT : 0 ≤ cT) (hdA : 0 ≤ dA) (hdH : 0 ≤ dH) (hhb : 0 ≤ hb) (htt : 0 ≤ tt)
    (h48 : 48 * K ^ 2 ≤ cH ^ 4) (h5670 : 5670 * K ^ 4 ≤ cT ^ 4)
    (hHb : frobH Hbar ≤ hb ^ 2) (hTt : frobT D.T ≤ tt ^ 2)
    (hk : ∀ᵐ x ∂D.ν, kA D.ψ x ≤ K * t)
    (hA : ∫ x, (nsq (fun i => AxC D.ℓ D.H D.T D.mu D.ψ x i - Abar i)) ^ 2 ∂D.ν ≤ dA ^ 4)
    (hH : ∫ x, (frobH (HxC D.H D.T D.mu x - Hbar)) ^ 2 ∂D.ν ≤ dH ^ 4) :
    D4C D.ν D.ℓ D.H D.T D.mu D.ψ Abar ≤ (dA + cH * rt * (hb + dH) + cT * t * tt) ^ 4 := by
  have hprob := D.hν.prob
  have ht0 : 0 ≤ t := ht ▸ sq_nonneg rt
  have hKt : 0 ≤ K * t := mul_nonneg hK ht0
  -- continuity in `x`
  have cA (i : Fin n) : Continuous fun x => AxC D.ℓ D.H D.T D.mu D.ψ x i - Abar i := by
    simp only [AxC, aU3]
    exact (((continuous_const.add (continuous_const.mul
      (continuous_finsetSum _ fun j _ => continuous_const.mul (D.cmu j)))).add
      (continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
        (continuous_const.mul (D.cmu j)).mul (D.cmu k)))).add
      ((continuous_const.mul (cont_kA D)).mul continuous_const)).sub continuous_const
  have cFa : Continuous fun x => (nsq (fun i => AxC D.ℓ D.H D.T D.mu D.ψ x i - Abar i)) ^ 2 := by
    simp only [nsq]
    exact (continuous_finsetSum _ fun i _ => (cA i).pow 2).pow 2
  have cFH : Continuous fun x => frobH (HxC D.H D.T D.mu x) ^ 2 := by
    simp only [frobH]
    exact (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (cont_Hx D i j).pow 2).pow 2
  have cFHd : Continuous fun x => frobH (HxC D.H D.T D.mu x - Hbar) ^ 2 := by
    simp only [frobH, Matrix.sub_apply]
    exact (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((cont_Hx D i j).sub continuous_const).pow 2).pow 2
  -- integrability on the product
  have iU := PP_int_prod ((PP.sum Finset.univ fun i _ => (PP_UpC D i).sq).sq) D.hν
  have iV := PP_int_prod ((PP.sum Finset.univ fun i _ => (PP_VpC D i).sq).sq) D.hν
  have iR := PP_int_prod (PP_R4 D Abar) D.hν
  simp only [map_pow, map_sum] at iU iV
  simp only [map_pow, map_sum, map_sub, eval_C, eval_GpC] at iR
  have iUx : Integrable (fun x => ∫ W, (∑ i, (eval W (UpC D i x)) ^ 2) ^ 2
      ∂stdGauss (J × Fin n)) D.ν := iU.integral_prod_left
  have iVx : Integrable (fun x => ∫ W, (∑ i, (eval W (VpC D i x)) ^ 2) ^ 2
      ∂stdGauss (J × Fin n)) D.ν := iV.integral_prod_left
  have iRx : Integrable (fun x => ∫ W, (∑ i, (GvC D i x W - Abar i) ^ 2) ^ 2
      ∂stdGauss (J × Fin n)) D.ν := iR.integral_prod_left
  have hswap : D4C D.ν D.ℓ D.H D.T D.mu D.ψ Abar =
      ∫ x, ∫ W, (∑ i, (GvC D i x W - Abar i) ^ 2) ^ 2 ∂stdGauss (J × Fin n) ∂D.ν := by
    rw [D4C_eq]; unfold d4C
    exact (integral_integral_swap
      (f := fun x W => (∑ i, (GvC D i x W - Abar i) ^ 2) ^ 2) iR).symm
  set IA := ∫ x, (nsq (fun i => AxC D.ℓ D.H D.T D.mu D.ψ x i - Abar i)) ^ 2 ∂D.ν with hIA
  set IU := ∫ x, ∫ W, (∑ i, (eval W (UpC D i x)) ^ 2) ^ 2 ∂stdGauss (J × Fin n) ∂D.ν with hIU
  set IV := ∫ x, ∫ W, (∑ i, (eval W (VpC D i x)) ^ 2) ^ 2 ∂stdGauss (J × Fin n) ∂D.ν with hIV
  -- the weighted bound
  have hcomb : ∀ l1 l2 l3 : ℝ, 0 < l1 → 0 < l2 → 0 < l3 → l1 + l2 + l3 = 1 →
      D4C D.ν D.ℓ D.H D.T D.mu D.ψ Abar ≤ IA / l1 ^ 3 + 16 * IU / l2 ^ 3 + 81 * IV / l3 ^ 3 := by
    intro l1 l2 l3 h1 h2 h3 hs
    have hpt (x : Fin n → ℝ) : ∫ W, (∑ i, (GvC D i x W - Abar i) ^ 2) ^ 2 ∂stdGauss (J × Fin n) ≤
        1 / l1 ^ 3 * (nsq (fun i => AxC D.ℓ D.H D.T D.mu D.ψ x i - Abar i)) ^ 2 +
        16 / l2 ^ 3 * (∫ W, (∑ i, (eval W (UpC D i x)) ^ 2) ^ 2 ∂stdGauss (J × Fin n)) +
        81 / l3 ^ 3 * ∫ W, (∑ i, (eval W (VpC D i x)) ^ 2) ^ 2 ∂stdGauss (J × Fin n) := by
      have iu : Integrable (fun W : J × Fin n → ℝ => (∑ i, (eval W (UpC D i x)) ^ 2) ^ 2)
          (stdGauss (J × Fin n)) := by
        have := gpi78 (∑ i, UpC D i x ^ 2) 2
        simpa only [map_sum, map_pow] using this
      have iv : Integrable (fun W : J × Fin n → ℝ => (∑ i, (eval W (VpC D i x)) ^ 2) ^ 2)
          (stdGauss (J × Fin n)) := by
        have := gpi78 (∑ i, VpC D i x ^ 2) 2
        simpa only [map_sum, map_pow] using this
      have ir : Integrable (fun W : J × Fin n → ℝ => (∑ i, (GvC D i x W - Abar i) ^ 2) ^ 2)
          (stdGauss (J × Fin n)) := by
        have := gpi78 (∑ i, (GpC D i x - C (Abar i)) ^ 2) 2
        simpa only [map_sum, map_pow, map_sub, eval_C, eval_GpC] using this
      have h := int3 (μ := stdGauss (J × Fin n))
        (fun W => (∑ i, (GvC D i x W - Abar i) ^ 2) ^ 2)
        (fun _ => (nsq (fun i => AxC D.ℓ D.H D.T D.mu D.ψ x i - Abar i)) ^ 2)
        (fun W => (∑ i, (eval W (UpC D i x)) ^ 2) ^ 2)
        (fun W => (∑ i, (eval W (VpC D i x)) ^ 2) ^ 2) (1 / l1 ^ 3) (16 / l2 ^ 3) (81 / l3 ^ 3)
        ir (integrable_const _) iu iv (fun W => by
          have t := tri4 (fun i => AxC D.ℓ D.H D.T D.mu D.ψ x i - Abar i)
            (fun i => 2 * eval W (UpC D i x)) (fun i => 3 * eval W (VpC D i x)) l1 l2 l3 h1 h2 h3 hs
          simp only [← G_decomp D hT Abar] at t
          have e2 : (∑ i, (2 * eval W (UpC D i x)) ^ 2) ^ 2 / l2 ^ 3 =
              16 / l2 ^ 3 * (∑ i, (eval W (UpC D i x)) ^ 2) ^ 2 := by
            simp only [mul_pow, ← Finset.mul_sum]; ring
          have e3 : (∑ i, (3 * eval W (VpC D i x)) ^ 2) ^ 2 / l3 ^ 3 =
              81 / l3 ^ 3 * (∑ i, (eval W (VpC D i x)) ^ 2) ^ 2 := by
            simp only [mul_pow, ← Finset.mul_sum]; ring
          have e1 : (∑ i, (AxC D.ℓ D.H D.T D.mu D.ψ x i - Abar i) ^ 2) ^ 2 / l1 ^ 3 =
              1 / l1 ^ 3 * (nsq (fun i => AxC D.ℓ D.H D.T D.mu D.ψ x i - Abar i)) ^ 2 := by
            simp only [nsq]; ring
          rw [e1, e2, e3] at t
          exact t)
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h
    have h := int3 (μ := D.ν)
      (fun x => ∫ W, (∑ i, (GvC D i x W - Abar i) ^ 2) ^ 2 ∂stdGauss (J × Fin n))
      (fun x => (nsq (fun i => AxC D.ℓ D.H D.T D.mu D.ψ x i - Abar i)) ^ 2)
      (fun x => ∫ W, (∑ i, (eval W (UpC D i x)) ^ 2) ^ 2 ∂stdGauss (J × Fin n))
      (fun x => ∫ W, (∑ i, (eval W (VpC D i x)) ^ 2) ^ 2 ∂stdGauss (J × Fin n))
      (1 / l1 ^ 3) (16 / l2 ^ 3) (81 / l3 ^ 3) iRx (sph_int D.hν cFa) iUx iVx hpt
    rw [hswap]
    refine h.trans (le_of_eq ?_)
    rw [← hIA, ← hIU, ← hIV]; ring
  -- the three bounds
  have hH4 : ∫ x, frobH (HxC D.H D.T D.mu x) ^ 2 ∂D.ν ≤ (hb + dH) ^ 4 := by
    have hc := comb3 (∫ x, frobH (HxC D.H D.T D.mu x) ^ 2 ∂D.ν) (hb ^ 4)
      (∫ x, (frobH (HxC D.H D.T D.mu x - Hbar)) ^ 2 ∂D.ν) 0 hb dH 0 hhb hdH le_rfl le_rfl hH
      (by norm_num) (fun l1 l2 l3 h1 h2 h3 hs => by
        have h := int3 (μ := D.ν) (fun x => frobH (HxC D.H D.T D.mu x) ^ 2) (fun _ => hb ^ 4)
          (fun x => (frobH (HxC D.H D.T D.mu x - Hbar)) ^ 2) (fun _ => 0)
          (1 / l1 ^ 3) (1 / l2 ^ 3) 0 (sph_int D.hν cFH) (integrable_const _)
          (sph_int D.hν cFHd) (integrable_const _) (fun x => by
            have f := frob_tri (HxC D.H D.T D.mu x) Hbar l1 l2 l3 h1 h2 h3 hs
            have q : frobH Hbar ^ 2 ≤ hb ^ 4 := by
              have := pow_le_pow_left₀ (frobH_nonneg Hbar) hHb 2
              refine this.trans (le_of_eq ?_); ring
            have q' := div_le_div_of_nonneg_right q (by positivity : (0:ℝ) ≤ l1 ^ 3)
            have e1 : 1 / l1 ^ 3 * hb ^ 4 = hb ^ 4 / l1 ^ 3 := by ring
            have e2 : 1 / l2 ^ 3 * (frobH (HxC D.H D.T D.mu x - Hbar)) ^ 2 =
                (frobH (HxC D.H D.T D.mu x - Hbar)) ^ 2 / l2 ^ 3 := by ring
            show _ ≤ 1 / l1 ^ 3 * hb ^ 4 + 1 / l2 ^ 3 * (frobH (HxC D.H D.T D.mu x - Hbar)) ^ 2 +
              0 * 0
            rw [e1, e2]; linarith)
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, zero_mul, add_zero] at h
        refine h.trans (le_of_eq ?_); ring)
    simpa using hc
  have hIU' : IU ≤ 3 * (K * t) ^ 2 * (hb + dH) ^ 4 := by
    have h1 : IU ≤ ∫ x, 3 * (K * t) ^ 2 * frobH (HxC D.H D.T D.mu x) ^ 2 ∂D.ν := by
      refine integral_mono_ae iUx ((sph_int D.hν cFH).const_mul _) ?_
      filter_upwards [hk] with x hx
      refine (U_x D x).trans ?_
      have hk2 : kA D.ψ x ^ 2 ≤ (K * t) ^ 2 := pow_le_pow_left₀ (kA_nonneg D x) hx 2
      have : (kA D.ψ x * frobH (HxC D.H D.T D.mu x)) ^ 2 ≤
          (K * t) ^ 2 * frobH (HxC D.H D.T D.mu x) ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right hk2 (sq_nonneg _)
      linarith
    rw [integral_const_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hH4 (by positivity))
  have hIV' : IV ≤ 35 / 2 * (2 * (K * t) ^ 2 * tt ^ 2) ^ 2 := by
    have h1 : IV ≤ ∫ _x, 35 / 2 * (2 * (K * t) ^ 2 * tt ^ 2) ^ 2 ∂D.ν := by
      refine integral_mono_ae iVx (integrable_const _) ?_
      filter_upwards [hk] with x hx
      refine (V_x D hT x).trans ?_
      have hk2 : kA D.ψ x ^ 2 ≤ (K * t) ^ 2 := pow_le_pow_left₀ (kA_nonneg D x) hx 2
      have hf0 : 0 ≤ frobT D.T :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          Finset.sum_nonneg fun l _ => sq_nonneg _
      have hm : 2 * kA D.ψ x ^ 2 * frobT D.T ≤ 2 * (K * t) ^ 2 * tt ^ 2 :=
        mul_le_mul (by linarith) hTt hf0 (by positivity)
      have := pow_le_pow_left₀ (mul_nonneg (by positivity) hf0) hm 2
      linarith
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h1
  have hQ : 16 * IU ≤ (cH * rt * (hb + dH)) ^ 4 := by
    have e : (cH * rt * (hb + dH)) ^ 4 = cH ^ 4 * (t ^ 2 * (hb + dH) ^ 4) := by
      rw [← ht]; ring
    have := mul_le_mul_of_nonneg_right h48 (by positivity : 0 ≤ t ^ 2 * (hb + dH) ^ 4)
    rw [e]; nlinarith
  have hR : 81 * IV ≤ (cT * t * tt) ^ 4 := by
    have e : (cT * t * tt) ^ 4 = cT ^ 4 * (t ^ 4 * tt ^ 4) := by ring
    have := mul_le_mul_of_nonneg_right h5670 (by positivity : 0 ≤ t ^ 4 * tt ^ 4)
    rw [e]; nlinarith
  exact comb3 _ IA (16 * IU) (81 * IV) dA (cH * rt * (hb + dH)) (cT * t * tt) hdA
    (by positivity) (mul_nonneg (mul_nonneg hcT ht0) htt) hA hQ hR hcomb

/-- **The fourth moment of the gradient fluctuation.** -/
theorem gradL4 : GradL4 := by
  intro n J _ ν hν ℓ H hH T hT mu ψ hmu hψ Abar Hbar K t rt cH cT dA dH hb tt hK hrt ht hcH hcT
    hdA hdH hhb htt h48 h5670 hHb hTt hk hA hHd
  exact gradL4_D ⟨ν, hν, 0, ℓ, H, T, mu, ψ, hmu, hψ⟩ hT Abar Hbar K t rt cH cT dA dH hb tt hK hrt
    ht hcH hcT hdA hdH hhb htt h48 h5670 hHb hTt hk hA hHd

end BstLean.Part90

#print axioms BstLean.Part90.gradL4
