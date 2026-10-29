import BstLean.Part80Defs
import BstLean.Part80Defs2
import BstLean.Part78Var3
import BstLean.Part78Poincare
import BstLean.Part78Deg2
import BstLean.Part78Wick

/-!
# Part 80: the conditional variance bound `VarBoundA` (Gaussian Poincaré route)

`Var_W V ≤ 4 Γ (4184/1000) ((1+η) S + (1+1/η)(8·1733/1000) ‖H‖_F²) V̄` for a general probability
distribution `ν` on the sphere, continuous features `ψ` and a continuous mean field `mu`.
The structure follows `Part78VarA/B/C`, `Part78Var`, `Part78Var2`.
-/

namespace BstLean.Part80

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (varU)
open BstLean.Part48 (gauss_poly_integrable)
open BstLean.Part78 (nsq frobH trH qfun aU zv PP gpi78 holder_pt2 aff_second)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ### Integration of `PP` families against a distribution on the sphere -/

lemma sph_int {n : ℕ} {ν : Measure (Fin n → ℝ)} (hν : SphLaw n ν) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f ν := by
  have := hν.prob
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hν.sphere] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

section pp
variable {n : ℕ} {ι : Type} [Fintype ι] {ν : Measure (Fin n → ℝ)}

lemma PP_int_x {d : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) (hν : SphLaw n ν)
    (W : ι → ℝ) : Integrable (fun x : Fin n → ℝ => eval W (A x)) ν :=
  sph_int hν (hA.cont_x W)

lemma PP_int_prod {d : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) (hν : SphLaw n ν) :
    Integrable (fun p : (Fin n → ℝ) × (ι → ℝ) => eval p.2 (A p.1)) (ν.prod (stdGauss ι)) := by
  have := hν.prob
  obtain ⟨S, _, b, M, hb, hM, hA⟩ := hA
  simp only [hA, map_sum, map_mul, eval_C]
  refine integrable_finsetSum _ fun s _ => ?_
  exact (sph_int hν (hb s)).mul_prod (gauss_poly_integrable (M s))

lemma PP_int {d : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) (hν : SphLaw n ν) :
    ∃ Abar : MvPolynomial ι ℝ, Abar.totalDegree ≤ d ∧
      (∀ W, eval W Abar = ∫ x, eval W (A x) ∂ν) ∧
      ∀ α W, eval W (pderiv α Abar) = ∫ x, eval W (pderiv α (A x)) ∂ν := by
  obtain ⟨S, _, b, M, hb, hM, hA⟩ := hA
  refine ⟨∑ s, C (∫ x, b s x ∂ν) * M s, ?_, ?_, ?_⟩
  · refine totalDegree_finsetSum_le fun s _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    simpa using hM s
  · intro W
    simp only [hA, map_sum, map_mul, eval_C]
    rw [integral_finsetSum _ fun s _ => (sph_int hν (hb s)).mul_const _]
    exact Finset.sum_congr rfl fun s _ => (integral_mul_const _ _).symm
  · intro α W
    simp only [hA, map_sum, Derivation.leibniz, pderiv_C, smul_eq_mul, mul_zero, add_zero,
      map_mul, eval_C]
    rw [integral_finsetSum _ fun s _ => (sph_int hν (hb s)).mul_const _]
    exact Finset.sum_congr rfl fun s _ => (integral_mul_const _ _).symm

end pp

/-! ### Bessel with the feature operator bound -/

lemma besselVB {n : ℕ} {J : Type} [Fintype J] {ν : Measure (Fin n → ℝ)} (hν : SphLaw n ν)
    {ψ : (Fin n → ℝ) → J → ℝ} (hψ : Continuous ψ) (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hF : FeatOpA ν ψ lam) (r : (Fin n → ℝ) → ℝ) (hr : Continuous r) :
    ∑ q : J, (∫ x, r x * ψ x q ∂ν) ^ 2 ≤ lam * ∫ x, r x ^ 2 ∂ν := by
  have hψq (q : J) : Continuous fun x => ψ x q := (continuous_apply q).comp hψ
  set c : J → ℝ := fun q => ∫ x, r x * ψ x q ∂ν with hc
  set g : (Fin n → ℝ) → ℝ := fun x => ∑ q, c q * ψ x q with hg
  have hgc : Continuous g := continuous_finsetSum _ fun q _ => continuous_const.mul (hψq q)
  set S := ∑ q : J, c q ^ 2 with hS
  set R := ∫ x, r x ^ 2 ∂ν with hR
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun q _ => sq_nonneg _
  have hrg : ∫ x, r x * g x ∂ν = S := by
    have he : (fun x => r x * g x) = fun x => ∑ q, c q * (r x * ψ x q) := by
      funext x; simp only [hg, Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
    have hi (q : J) : Integrable (fun x => c q * (r x * ψ x q)) ν :=
      (sph_int hν (hr.mul (hψq q))).const_mul _
    rw [he, integral_finsetSum _ fun q _ => hi q]
    simp only [integral_const_mul, hS]
    exact Finset.sum_congr rfl fun q _ => by simp only [hc]; ring
  have hgg : ∫ x, g x ^ 2 ∂ν ≤ lam * S := hF c
  have hquad (t : ℝ) : 0 ≤ t ^ 2 * (lam * S) - 2 * t * S + R := by
    have h : 0 ≤ ∫ x, (t * g x - r x) ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have he : (fun x => (t * g x - r x) ^ 2) = fun x =>
        (t ^ 2 * g x ^ 2 - (2 * t) * (r x * g x)) + r x ^ 2 := by funext x; ring
    have i1 : Integrable (fun x => t ^ 2 * g x ^ 2) ν := (sph_int hν (hgc.pow 2)).const_mul _
    have i2 : Integrable (fun x => (2 * t) * (r x * g x)) ν :=
      (sph_int hν (hr.mul hgc)).const_mul _
    have i3 : Integrable (fun x => r x ^ 2) ν := sph_int hν (hr.pow 2)
    have i12 : Integrable (fun x => t ^ 2 * g x ^ 2 - (2 * t) * (r x * g x)) ν := i1.sub i2
    rw [he, integral_add i12 i3, integral_sub i1 i2, integral_const_mul,
      integral_const_mul, hrg] at h
    nlinarith [sq_nonneg t]
  rcases hlam0.lt_or_eq with hpos | hzero
  · have h := hquad (1 / lam)
    have e : (1 / lam) ^ 2 * (lam * S) - 2 * (1 / lam) * S + R = R - S / lam := by
      field_simp; ring
    rw [e] at h
    have : S / lam ≤ R := by linarith
    rw [div_le_iff₀ hpos] at this
    linarith
  · rw [← hzero, zero_mul]
    by_contra hcon
    rw [not_le] at hcon
    have h := hquad ((R + 1) / (2 * S))
    rw [← hzero] at h
    have e : (R + 1) / (2 * S) * S = (R + 1) / 2 := by field_simp
    nlinarith

/-! ### The data and the polynomials -/

/-- The data of the abstract conditional model. -/
structure Dat (n : ℕ) (J : Type) [Fintype J] where
  ν : Measure (Fin n → ℝ)
  hν : SphLaw n ν
  f0 : ℝ
  ℓ : Fin n → ℝ
  H : Matrix (Fin n) (Fin n) ℝ
  hH : H.IsSymm
  mu : (Fin n → ℝ) → Fin n → ℝ
  ψ : (Fin n → ℝ) → J → ℝ
  hmu : Continuous mu
  hψ : Continuous ψ

variable {n : ℕ} {J : Type} [Fintype J] (D : Dat n J)

lemma Dat.cψ (q : J) : Continuous fun x => D.ψ x q := (continuous_apply q).comp D.hψ
lemma Dat.cmu (i : Fin n) : Continuous fun x => D.mu x i := (continuous_apply i).comp D.hmu

/-- `z_i` as a polynomial in `W`. -/
noncomputable def ZpA (x : Fin n → ℝ) (i : Fin n) : MvPolynomial (J × Fin n) ℝ :=
  ∑ q : J, C (D.ψ x q) * X (q, i)

/-- `mu_i(x) + z_i` as a polynomial in `W`. -/
noncomputable def YpA (x : Fin n → ℝ) (i : Fin n) : MvPolynomial (J × Fin n) ℝ :=
  C (D.mu x i) + ZpA D x i

/-- `F_W(x)` as a polynomial in `W`. -/
noncomputable def FpA (x : Fin n → ℝ) : MvPolynomial (J × Fin n) ℝ :=
  C D.f0 + ∑ i, C (D.ℓ i) * YpA D x i + ∑ i, ∑ j, C (D.H i j) * YpA D x i * YpA D x j

/-- `(H z)_i` as a polynomial in `W`. -/
noncomputable def LpA (i : Fin n) (x : Fin n → ℝ) : MvPolynomial (J × Fin n) ℝ :=
  ∑ j, C (D.H i j) * ZpA D x j

/-- `T_i = a_i(x) + 2 Σ_j H_ij z_j`. -/
def TvA (i : Fin n) (x : Fin n → ℝ) (W : J × Fin n → ℝ) : ℝ :=
  aA D.ℓ D.H D.mu x i + 2 * ∑ j, D.H i j * zv W (D.ψ x) j

/-- `T_i` as a polynomial in `W`. -/
noncomputable def TpA (i : Fin n) (x : Fin n → ℝ) : MvPolynomial (J × Fin n) ℝ :=
  C (aA D.ℓ D.H D.mu x i) + C 2 * LpA D i x

@[simp] lemma eval_ZpA (x : Fin n → ℝ) (i : Fin n) (W : J × Fin n → ℝ) :
    eval W (ZpA D x i) = zv W (D.ψ x) i := by
  simp only [ZpA, zv, map_sum, map_mul, eval_C, eval_X]
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

@[simp] lemma eval_FpA (x : Fin n → ℝ) (W : J × Fin n → ℝ) :
    eval W (FpA D x) = FA D.f0 D.ℓ D.H D.mu D.ψ W x := by
  simp only [FpA, YpA, FA, qfun, map_sum, map_add, map_mul, eval_C, eval_ZpA]

@[simp] lemma eval_LpA (i : Fin n) (x : Fin n → ℝ) (W : J × Fin n → ℝ) :
    eval W (LpA D i x) = ∑ j, D.H i j * zv W (D.ψ x) j := by
  simp only [LpA, map_sum, map_mul, eval_C, eval_ZpA]

@[simp] lemma eval_TpA (i : Fin n) (x : Fin n → ℝ) (W : J × Fin n → ℝ) :
    eval W (TpA D i x) = TvA D i x W := by
  simp only [TpA, TvA, map_add, map_mul, eval_C, eval_LpA]

lemma Lv_lin (i : Fin n) (x : Fin n → ℝ) (W : J × Fin n → ℝ) :
    ∑ j, D.H i j * zv W (D.ψ x) j = ∑ β : J × Fin n, (D.H i β.2 * D.ψ x β.1) * W β := by
  unfold zv
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

lemma pderiv_ZpA (x : Fin n → ℝ) (q : J) (i j : Fin n) :
    pderiv (q, i) (ZpA D x j) = if j = i then C (D.ψ x q) else 0 := by
  classical
  simp only [ZpA, map_sum, Derivation.leibniz, pderiv_C, pderiv_X, Pi.single_apply, Prod.mk.injEq,
    smul_eq_mul, mul_zero, add_zero]
  by_cases h : j = i <;> simp [h]

lemma pderiv_YpA (x : Fin n → ℝ) (q : J) (i j : Fin n) :
    pderiv (q, i) (YpA D x j) = if j = i then C (D.ψ x q) else 0 := by
  simp only [YpA, map_add, pderiv_C, zero_add, pderiv_ZpA]

lemma eval_YpA (x : Fin n → ℝ) (i : Fin n) (W : J × Fin n → ℝ) :
    eval W (YpA D x i) = D.mu x i + zv W (D.ψ x) i := by
  simp only [YpA, map_add, eval_C, eval_ZpA]

lemma eval_pderiv_FpA (x : Fin n → ℝ) (q : J) (i : Fin n) (W : J × Fin n → ℝ) :
    eval W (pderiv (q, i) (FpA D x)) = D.ψ x q * TvA D i x W := by
  classical
  have hs : ∀ k, D.H k i = D.H i k := fun k => by
    have := congrFun (congrFun D.hH i) k; simpa [Matrix.transpose_apply] using this
  simp only [FpA, TvA, aA, aU, map_sum, map_add, Derivation.leibniz, pderiv_C, pderiv_YpA,
    smul_eq_mul,
    mul_zero, add_zero, map_mul, eval_C, eval_YpA, mul_ite, apply_ite (eval W), map_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ite_mul, zero_mul, zero_add]
  simp only [hs, mul_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [add_assoc, mul_comm (D.ℓ i)]
  congr 1
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma PP_ZpA (i : Fin n) : PP 1 (fun x : Fin n → ℝ => ZpA D x i) := by
  unfold ZpA
  refine PP.sum _ fun q _ => ?_
  have := (PP.coef (ι := J × Fin n) (D.cψ q)).mul
    (PP.const (n := n) (d := 1) (X (q, i) : MvPolynomial (J × Fin n) ℝ) (by simp))
  simpa using this

lemma PP_Cc (c : ℝ) : PP (n := n) 0 (fun _ => (C c : MvPolynomial (J × Fin n) ℝ)) :=
  PP.const _ (by simp)

lemma PP_YpA (i : Fin n) : PP 1 (fun x : Fin n → ℝ => YpA D x i) := by
  unfold YpA
  exact ((PP.coef (ι := J × Fin n) (D.cmu i)).mono (by norm_num)).add (PP_ZpA D i)

lemma PP_FpA : PP 2 (FpA D) := by
  unfold FpA
  refine PP.add (PP.add ((PP_Cc D.f0).mono (by norm_num)) (PP.sum _ fun i _ => ?_))
    (PP.sum _ fun i _ => PP.sum _ fun j _ => ?_)
  · exact (((PP_Cc (D.ℓ i)).mul (PP_YpA D i))).mono (by norm_num)
  · exact ((((PP_Cc (D.H i j)).mul (PP_YpA D i))).mul (PP_YpA D j)).mono (by norm_num)

lemma PP_LpA (i : Fin n) : PP 1 (LpA D i) := by
  unfold LpA
  exact PP.sum _ fun j _ => ((PP_Cc (D.H i j)).mul (PP_ZpA D j)).mono (by norm_num)

lemma cont_aVB (i : Fin n) : Continuous fun x => aA D.ℓ D.H D.mu x i := by
  unfold aA aU
  exact continuous_const.add (continuous_const.mul
    (continuous_finsetSum _ fun j _ => continuous_const.mul (D.cmu j)))

lemma PP_TpA (i : Fin n) : PP 1 (TpA D i) := by
  unfold TpA
  refine PP.add ((PP.coef (ι := J × Fin n) (cont_aVB D i)).mono (by norm_num)) ?_
  exact ((PP_Cc (n := n) (J := J) 2).mul (PP_LpA D i)).mono (by norm_num)

/-! ### The mean, `Q_x`, and `V` as polynomials -/

/-- `E_y F_W(y)` as a polynomial in `W`. -/
noncomputable def FbarA : MvPolynomial (J × Fin n) ℝ := Classical.choose (PP_int (PP_FpA D) D.hν)

lemma FbarA_deg : (FbarA D).totalDegree ≤ 2 := (Classical.choose_spec (PP_int (PP_FpA D) D.hν)).1

lemma FbarA_eval (W : J × Fin n → ℝ) :
    eval W (FbarA D) = ∫ x, FA D.f0 D.ℓ D.H D.mu D.ψ W x ∂D.ν := by
  have := (Classical.choose_spec (PP_int (PP_FpA D) D.hν)).2.1 W
  unfold FbarA
  simpa only [eval_FpA] using this

/-- `Q_x = F_x − E_y F_y`. -/
noncomputable def QpA (x : Fin n → ℝ) : MvPolynomial (J × Fin n) ℝ := FpA D x - FbarA D

lemma PP_QpA : PP 2 (QpA D) := (PP_FpA D).sub (PP.const _ (FbarA_deg D))

lemma QpA_mean (W : J × Fin n → ℝ) : ∫ x, eval W (QpA D x) ∂D.ν = 0 := by
  have := D.hν.prob
  have he : (fun x => eval W (QpA D x)) =
      fun x => FA D.f0 D.ℓ D.H D.mu D.ψ W x - eval W (FbarA D) := by
    funext x; simp [QpA]
  have hi : Integrable (fun x => FA D.f0 D.ℓ D.H D.mu D.ψ W x) D.ν := by
    have := PP_int_x (PP_FpA D) D.hν W
    simpa only [eval_FpA] using this
  rw [he, integral_sub hi (integrable_const _), integral_const, FbarA_eval]
  simp

/-- `V` as a polynomial in `W`. -/
noncomputable def PVA : MvPolynomial (J × Fin n) ℝ :=
  Classical.choose (PP_int (PP_QpA D).sq D.hν)

lemma PVA_eval (W : J × Fin n → ℝ) :
    eval W (PVA D) = VA D.ν D.f0 D.ℓ D.H D.mu D.ψ W := by
  have := (Classical.choose_spec (PP_int (PP_QpA D).sq D.hν)).2.1 W
  rw [PVA, this]
  simp [VA, varU, QpA, FbarA_eval]

lemma PVA_eval' (W : J × Fin n → ℝ) :
    VA D.ν D.f0 D.ℓ D.H D.mu D.ψ W = ∫ x, (eval W (QpA D x)) ^ 2 ∂D.ν := by
  have := (Classical.choose_spec (PP_int (PP_QpA D).sq D.hν)).2.1 W
  rw [← PVA_eval D, PVA, this]
  simp

lemma cont_QT (i : Fin n) (W : J × Fin n → ℝ) :
    Continuous fun x => eval W (QpA D x) * TvA D i x W := by
  refine ((PP_QpA D).cont_x W).mul ?_
  have := (PP_TpA D i).cont_x W
  simpa only [eval_TpA] using this

/-- The gradient of `V`. -/
lemma PVA_grad (q : J) (i : Fin n) (W : J × Fin n → ℝ) :
    eval W (pderiv (q, i) (PVA D)) =
      2 * ∫ x, (eval W (QpA D x) * TvA D i x W) * D.ψ x q ∂D.ν := by
  have h := (Classical.choose_spec (PP_int (PP_QpA D).sq D.hν)).2.2 (q, i) W
  rw [PVA, h]
  set cW := eval W (pderiv (q, i) (FbarA D)) with hcW
  have e : (fun x => eval W (pderiv (q, i) (QpA D x ^ 2))) = fun x =>
      2 * ((eval W (QpA D x) * TvA D i x W) * D.ψ x q) - (2 * cW) * eval W (QpA D x) := by
    funext x
    have h1 : eval W (pderiv (q, i) (QpA D x)) = D.ψ x q * TvA D i x W - cW := by
      simp only [QpA, map_sub, eval_pderiv_FpA D, hcW]
    rw [pow_two, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, h1]
    ring
  have i1 : Integrable (fun x => 2 * ((eval W (QpA D x) * TvA D i x W) * D.ψ x q)) D.ν :=
    (sph_int D.hν ((cont_QT D i W).mul (D.cψ q))).const_mul _
  have i2 : Integrable (fun x => (2 * cW) * eval W (QpA D x)) D.ν :=
    (PP_int_x (PP_QpA D) D.hν W).const_mul _
  rw [e, integral_sub i1 i2, integral_const_mul, integral_const_mul, QpA_mean]
  ring

lemma PP_RA (i : Fin n) : PP ((2 + 1) + (2 + 1)) (fun x => (QpA D x * TpA D i x) ^ 2) :=
  ((PP_QpA D).mul (PP_TpA D i)).sq

/-- Bessel, for each `W` and `i`. -/
lemma grad_sq_leA (Γ : ℝ) (hΓ : 0 ≤ Γ) (hF : FeatOpA D.ν D.ψ Γ) (i : Fin n)
    (W : J × Fin n → ℝ) :
    ∑ q : J, (eval W (pderiv (q, i) (PVA D))) ^ 2 ≤
      4 * Γ * ∫ x, (eval W (QpA D x) * TvA D i x W) ^ 2 ∂D.ν := by
  have hb := besselVB D.hν D.hψ Γ hΓ hF _ (cont_QT D i W)
  have e : ∀ y : ℝ, (2 * y) ^ 2 = 4 * y ^ 2 := fun y => by ring
  simp only [PVA_grad D, e]
  rw [← Finset.mul_sum, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

lemma int_GA (i : Fin n) :
    Integrable (fun x => ∫ W, (eval W (QpA D x) * TvA D i x W) ^ 2 ∂stdGauss (J × Fin n))
      D.ν := by
  have := D.hν.prob
  have h := (PP_int_prod (PP_RA D i) D.hν).integral_prod_left
  simpa only [map_pow, map_mul, eval_TpA] using h

lemma swap_GA (i : Fin n) :
    ∫ x, ∫ W, (eval W (QpA D x) * TvA D i x W) ^ 2 ∂stdGauss (J × Fin n) ∂D.ν =
      ∫ W, ∫ x, (eval W (QpA D x) * TvA D i x W) ^ 2 ∂D.ν ∂stdGauss (J × Fin n) := by
  have := D.hν.prob
  have hI := PP_int_prod (PP_RA D i) D.hν
  have h := integral_integral_swap
    (f := fun (x : Fin n → ℝ) (W : J × Fin n → ℝ) => eval W ((QpA D x * TpA D i x) ^ 2)) hI
  simpa only [map_pow, map_mul, eval_TpA] using h

lemma int_GA_W (i : Fin n) :
    Integrable (fun W => ∫ x, (eval W (QpA D x) * TvA D i x W) ^ 2 ∂D.ν)
      (stdGauss (J × Fin n)) := by
  have := D.hν.prob
  have h := (PP_int_prod (PP_RA D i) D.hν).integral_prod_right
  simpa only [map_pow, map_mul, eval_TpA] using h

lemma int_Q2A :
    Integrable (fun x => ∫ W, (eval W (QpA D x)) ^ 2 ∂stdGauss (J × Fin n)) D.ν := by
  have := D.hν.prob
  have h := (PP_int_prod (PP_QpA D).sq D.hν).integral_prod_left
  simpa only [map_pow] using h

lemma swap_Q2A :
    ∫ x, ∫ W, (eval W (QpA D x)) ^ 2 ∂stdGauss (J × Fin n) ∂D.ν =
      VbarA D.ν D.f0 D.ℓ D.H D.mu D.ψ := by
  have := D.hν.prob
  have hI := PP_int_prod (PP_QpA D).sq D.hν
  have h := integral_integral_swap
    (f := fun (x : Fin n → ℝ) (W : J × Fin n → ℝ) => eval W ((QpA D x) ^ 2)) hI
  simp only [map_pow] at h
  rw [h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun W => (PVA_eval' D W).symm)

/-! ### The pointwise bound -/

/-- `E_W (HR)_i² = (Σ_j H_ij²) k(x)`. -/
lemma Lv_second (i : Fin n) (x : Fin n → ℝ) :
    ∫ W, (eval W (LpA D i x)) ^ 2 ∂stdGauss (J × Fin n) = (∑ j, D.H i j ^ 2) * kA D.ψ x := by
  have h := aff_second BstLean.Part78.gaussLin (ι := J × Fin n) 0
    (fun β => D.H i β.2 * D.ψ x β.1)
  simp only [zero_add] at h
  simp only [eval_LpA, Lv_lin]
  rw [h, Fintype.sum_prod_type, Finset.sum_comm]
  unfold kA
  rw [Finset.sum_mul_sum]
  simp
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_congr rfl fun q _ => by ring

lemma sq_split (η a L : ℝ) (hη : 0 < η) :
    (a + 2 * L) ^ 2 ≤ (1 + η) * a ^ 2 + (1 + 1 / η) * (4 * L ^ 2) := by
  have h : (1 + η) * a ^ 2 + (1 + 1 / η) * (4 * L ^ 2) - (a + 2 * L) ^ 2 =
      (η * a - 2 * L) ^ 2 / η := by field_simp; ring
  have : 0 ≤ (η * a - 2 * L) ^ 2 / η := by positivity
  linarith

lemma pointwiseA (x : Fin n → ℝ) (S η : ℝ) (hη : 0 < η) (hS : nsq (aA D.ℓ D.H D.mu x) ≤ S)
    (hk : kA D.ψ x ≤ 2) :
    ∑ i, ∫ W, (eval W (QpA D x) * TvA D i x W) ^ 2 ∂stdGauss (J × Fin n) ≤
      ((1 + η) * S + (1 + 1 / η) * ((4184 / 1000) * (8 * (1733 / 1000))) * frobH D.H) *
        ∫ W, (eval W (QpA D x)) ^ 2 ∂stdGauss (J × Fin n) := by
  set u2 := ∫ W, (eval W (QpA D x)) ^ 2 ∂stdGauss (J × Fin n) with hu2
  have hu0 : 0 ≤ u2 := integral_nonneg fun W => sq_nonneg _
  have hfr : ∀ i, 0 ≤ ∑ j, D.H i j ^ 2 := fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hk0 : 0 ≤ kA D.ψ x := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hη1 : 0 ≤ 1 + 1 / η := by positivity
  have hi (i : Fin n) : ∫ W, (eval W (QpA D x) * TvA D i x W) ^ 2 ∂stdGauss (J × Fin n) ≤
      (1 + η) * (aA D.ℓ D.H D.mu x i) ^ 2 * u2 + (1 + 1 / η) * (4 *
        ((4184 / 1000) * (1733 / 1000) * u2 * ((∑ j, D.H i j ^ 2) * kA D.ψ x))) := by
    have hT : ∫ z, (eval z (LpA D i x)) ^ 4 ∂stdGauss (J × Fin n) ≤
        (1733 / 1000 : ℝ) ^ 2 * (∫ z, (eval z (LpA D i x)) ^ 2 ∂stdGauss (J × Fin n)) ^ 2 := by
      have h := BstLean.Part78.affFourth3 (J × Fin n) 0 (fun β => D.H i β.2 * D.ψ x β.1)
      simp only [zero_add] at h
      simp only [eval_LpA, Lv_lin]
      exact h.trans (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _))
    have hU : ∫ z, (eval z (QpA D x)) ^ 4 ∂stdGauss (J × Fin n) ≤
        (4184 / 1000 : ℝ) ^ 2 * (∫ z, (eval z (QpA D x)) ^ 2 ∂stdGauss (J × Fin n)) ^ 2 :=
      (BstLean.Part78.deg2Fourth (J × Fin n) (QpA D x) ((PP_QpA D).deg x)).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _))
    have hh := holder_pt2 (QpA D x) (LpA D i x) (1733 / 1000) (4184 / 1000) (by norm_num)
      (by norm_num) hU hT
    rw [Lv_second, ← hu2] at hh
    have i1 : Integrable (fun W => (1 + η) * (aA D.ℓ D.H D.mu x i) ^ 2 * (eval W (QpA D x)) ^ 2)
        (stdGauss (J × Fin n)) := (gpi78 _ 2).const_mul _
    have i2 : Integrable (fun W => (1 + 1 / η) * (4 * ((eval W (QpA D x)) ^ 2 *
        (eval W (LpA D i x)) ^ 2))) (stdGauss (J × Fin n)) := by
      have := gauss_poly_integrable ((QpA D x) ^ 2 * (LpA D i x) ^ 2)
      simp only [map_mul, map_pow] at this
      exact (this.const_mul _).const_mul _
    have hle : ∫ W, (eval W (QpA D x) * TvA D i x W) ^ 2 ∂stdGauss (J × Fin n) ≤
        ∫ W, ((1 + η) * (aA D.ℓ D.H D.mu x i) ^ 2 * (eval W (QpA D x)) ^ 2 +
          (1 + 1 / η) * (4 * ((eval W (QpA D x)) ^ 2 * (eval W (LpA D i x)) ^ 2)))
          ∂stdGauss (J × Fin n) := by
      refine integral_mono ?_ (i1.add i2) fun W => ?_
      · have := gauss_poly_integrable ((QpA D x * TpA D i x) ^ 2)
        simpa only [map_mul, map_pow, eval_TpA] using this
      · have h := sq_split η (aA D.ℓ D.H D.mu x i) (eval W (LpA D i x)) hη
        have hq : 0 ≤ (eval W (QpA D x)) ^ 2 := sq_nonneg _
        have := mul_le_mul_of_nonneg_left h hq
        simp only [TvA, eval_LpA] at this ⊢
        rw [mul_pow]
        linarith
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul, integral_const_mul] at hle
    refine hle.trans ?_
    rw [← hu2]
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 4)) hη1
    linarith
  refine (Finset.sum_le_sum fun i _ => hi i).trans ?_
  have hsum : ∑ i, ((1 + η) * (aA D.ℓ D.H D.mu x i) ^ 2 * u2 + (1 + 1 / η) * (4 *
        ((4184 / 1000) * (1733 / 1000) * u2 * ((∑ j, D.H i j ^ 2) * kA D.ψ x)))) =
      (1 + η) * nsq (aA D.ℓ D.H D.mu x) * u2 + (1 + 1 / η) * (4 *
        ((4184 / 1000) * (1733 / 1000) * u2 * (frobH D.H * kA D.ψ x))) := by
    simp only [nsq, frobH, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [hsum]
  have hF0 : 0 ≤ frobH D.H := Finset.sum_nonneg fun i _ => hfr i
  have hn0 : 0 ≤ nsq (aA D.ℓ D.H D.mu x) := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : (1 + η) * nsq (aA D.ℓ D.H D.mu x) * u2 ≤ ((1 + η) * S) * u2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS (by positivity)) hu0
  have h2 : (1 + 1 / η) * (4 * ((4184 / 1000) * (1733 / 1000) * u2 * (frobH D.H * kA D.ψ x))) ≤
      ((1 + 1 / η) * ((4184 / 1000) * (8 * (1733 / 1000))) * frobH D.H) * u2 := by
    have hk2 : u2 * (frobH D.H * kA D.ψ x) ≤ u2 * (frobH D.H * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk hF0) hu0
    have := mul_le_mul_of_nonneg_left hk2 hη1
    nlinarith [this]
  linarith

/-- The variance bound for a bundled model. -/
theorem varBound_D (Γ S η : ℝ) (hΓ : 0 ≤ Γ) (hη : 0 < η) (hF : FeatOpA D.ν D.ψ Γ)
    (hx : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → nsq (aA D.ℓ D.H D.mu x) ≤ S ∧ kA D.ψ x ≤ 2) :
    ∫ W, (VA D.ν D.f0 D.ℓ D.H D.mu D.ψ W - VbarA D.ν D.f0 D.ℓ D.H D.mu D.ψ) ^ 2
        ∂stdGauss (J × Fin n) ≤
      4 * Γ * ((1 + η) * S +
        (1 + 1 / η) * ((4184 / 1000) * (8 * (1733 / 1000))) * frobH D.H) *
          VbarA D.ν D.f0 D.ℓ D.H D.mu D.ψ := by
  have hprob := D.hν.prob
  have hpoin := BstLean.Part78.poincareMv (J × Fin n) (PVA D)
  simp only [PVA_eval] at hpoin
  refine hpoin.trans ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have step1 (i : Fin n) :
      ∑ q : J, ∫ z, (eval z (pderiv (q, i) (PVA D))) ^ 2 ∂stdGauss (J × Fin n) ≤
        4 * Γ * ∫ x, ∫ W, (eval W (QpA D x) * TvA D i x W) ^ 2
          ∂stdGauss (J × Fin n) ∂D.ν := by
    rw [← integral_finsetSum _ (fun q _ => gpi78 _ 2), swap_GA, ← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun q _ => gpi78 _ 2)
      ((int_GA_W D i).const_mul _) (fun W => grad_sq_leA D Γ hΓ hF i W)
  refine (Finset.sum_le_sum fun i _ => step1 i).trans ?_
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => int_GA D i)]
  have step2 : ∫ x, ∑ i, ∫ W, (eval W (QpA D x) * TvA D i x W) ^ 2
        ∂stdGauss (J × Fin n) ∂D.ν ≤
      ((1 + η) * S + (1 + 1 / η) * ((4184 / 1000) * (8 * (1733 / 1000))) * frobH D.H) *
        VbarA D.ν D.f0 D.ℓ D.H D.mu D.ψ := by
    rw [← swap_Q2A D, ← integral_const_mul]
    refine integral_mono_ae (integrable_finsetSum _ fun i _ => int_GA D i)
      ((int_Q2A D).const_mul _) ?_
    filter_upwards [D.hν.sphere] with x hxs
    exact pointwiseA D x S η hη (hx x hxs).1 (hx x hxs).2
  have h4 : 0 ≤ 4 * Γ := by positivity
  refine (mul_le_mul_of_nonneg_left step2 h4).trans (le_of_eq ?_)
  ring

/-- **The conditional variance bound**, Poincaré route. -/
theorem varBoundA2 : VarBoundA2 := by
  intro n J _ ν hν f0 ℓ H hH mu ψ hmu hψ Γ S η hΓ hη hF hx
  exact varBound_D ⟨ν, hν, f0, ℓ, H, hH, mu, ψ, hmu, hψ⟩ Γ S η hΓ hη hF hx

end BstLean.Part80

#print axioms BstLean.Part80.varBoundA2
