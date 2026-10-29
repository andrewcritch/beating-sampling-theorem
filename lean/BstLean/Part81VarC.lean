import BstLean.Part81Defs
import BstLean.Part78Var4

/-!
# Part 81, variance bound: degree-`d` port of the Part 78 chain (file C)
-/

namespace BstLean.Part81.VarP

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (varU)
open BstLean.Part48 (gauss_poly_integrable)
open BstLean.Part78 (PP gpi78 poly_cs78 aff_second sphere_cont_integrableB sphere_cont_integrable78
  holder_pt2 nsq frobH trH zv Phi GaussLin AffFourth Deg2Fourth PoincareMv PoincareMv2 WickTwoPoint
  lin bv zv_lin bv_dot lin2 lin2_int lin3 lin3_int cubic_zero)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {n d : ℕ}

lemma continuous_pf {n d : ℕ} (q : JJ n d) : Continuous fun x : Fin n → ℝ => pf x q := by
  unfold pf BstLean.Part41.phiM BstLean.Part36.monoVal
  exact continuous_multiset_prod _ fun i _ => continuous_apply i

lemma bessel {n d : ℕ} (hn : 1 ≤ n) (CF : ℝ) (hCF : 0 ≤ CF) (hF : FeatOp n d CF)
    (r : (Fin n → ℝ) → ℝ) (hr : Continuous r) :
    ∑ q : JJ n d, (∫ x, r x * pf x q ∂uniformSphere n) ^ 2 ≤
      CF / (n : ℝ) * ∫ x, r x ^ 2 ∂uniformSphere n := by
  set c : JJ n d → ℝ := fun q => ∫ x, r x * pf x q ∂uniformSphere n with hc
  set g : (Fin n → ℝ) → ℝ := fun x => ∑ q, c q * pf x q with hg
  have hgc : Continuous g := continuous_finsetSum _ fun q _ => continuous_const.mul (continuous_pf q)
  set S := ∑ q : JJ n d, c q ^ 2 with hS
  set R := ∫ x, r x ^ 2 ∂uniformSphere n with hR
  set lam := CF / (n : ℝ) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun q _ => sq_nonneg _
  have hrg : ∫ x, r x * g x ∂uniformSphere n = S := by
    have he : (fun x => r x * g x) = fun x => ∑ q, c q * (r x * pf x q) := by
      funext x; simp only [hg, Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
    have hi (q : JJ n d) : Integrable (fun x => c q * (r x * pf x q)) (uniformSphere n) :=
      (sphere_cont_integrableB hn (hr.mul (continuous_pf q))).const_mul _
    rw [he, integral_finsetSum _ fun q _ => hi q]
    simp only [integral_const_mul, hS]
    exact Finset.sum_congr rfl fun q _ => by simp only [hc]; ring
  have hgg : ∫ x, g x ^ 2 ∂uniformSphere n ≤ lam * S := hF c
  have hquad (t : ℝ) : 0 ≤ t ^ 2 * (lam * S) - 2 * t * S + R := by
    have h : 0 ≤ ∫ x, (t * g x - r x) ^ 2 ∂uniformSphere n := integral_nonneg fun x => sq_nonneg _
    have he : (fun x => (t * g x - r x) ^ 2) = fun x =>
        (t ^ 2 * g x ^ 2 - (2 * t) * (r x * g x)) + r x ^ 2 := by funext x; ring
    have i1 : Integrable (fun x => t ^ 2 * g x ^ 2) (uniformSphere n) :=
      (sphere_cont_integrableB hn (hgc.pow 2)).const_mul _
    have i2 : Integrable (fun x => (2 * t) * (r x * g x)) (uniformSphere n) :=
      (sphere_cont_integrableB hn (hr.mul hgc)).const_mul _
    have i3 : Integrable (fun x => r x ^ 2) (uniformSphere n) :=
      sphere_cont_integrableB hn (hr.pow 2)
    have i12 : Integrable (fun x => t ^ 2 * g x ^ 2 - (2 * t) * (r x * g x)) (uniformSphere n) :=
      i1.sub i2
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


/-- `z_i` as a polynomial in `W`. -/
noncomputable def Zp (x : Fin n → ℝ) (i : Fin n) : MvPolynomial (WIdx n d) ℝ :=
  ∑ q : JJ n d, C (pf x q) * X (q, i)

/-- `F_x` as a polynomial in `W`. -/
noncomputable def Fp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial (WIdx n d) ℝ :=
  ∑ i, C (a i) * Zp (d := d) x i + ∑ i, ∑ j, C (H i j) * Zp (d := d) x i * Zp (d := d) x j

/-- `T_i = a_i + 2 Σ_j H_ij z_j`. -/
noncomputable def Tv (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ)
    (W : WIdx n d → ℝ) : ℝ := a i + 2 * ∑ j, H i j * zv W (pf x) j

/-- `T_i` as a polynomial in `W`. -/
noncomputable def Tp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ) :
    MvPolynomial (WIdx n d) ℝ := C (a i) + C 2 * ∑ j, C (H i j) * Zp (d := d) x j

@[simp] lemma eval_Zp (x : Fin n → ℝ) (i : Fin n) (W : WIdx n d → ℝ) :
    eval W (Zp (d := d) x i) = zv W (pf x) i := by
  simp only [Zp, zv, map_sum, map_mul, eval_C, eval_X]
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

@[simp] lemma eval_Fp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (W : WIdx n d → ℝ) : eval W (Fp (d := d) a H x) = FG a H W x := by
  simp only [Fp, FG, Phi, map_sum, map_add, map_mul, eval_C, eval_Zp]

@[simp] lemma eval_Tp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ)
    (W : WIdx n d → ℝ) : eval W (Tp (d := d) a H i x) = Tv a H i x W := by
  simp only [Tp, Tv, map_sum, map_add, map_mul, eval_C, eval_Zp]

lemma pderiv_Zp (x : Fin n → ℝ) (q : JJ n d) (i j : Fin n) :
    pderiv (q, i) (Zp (d := d) x j) = if j = i then C (pf x q) else 0 := by
  classical
  simp only [Zp, map_sum, Derivation.leibniz, pderiv_C, pderiv_X, Pi.single_apply, Prod.mk.injEq,
    smul_eq_mul, mul_zero, add_zero]
  by_cases h : j = i <;> simp [h]

lemma eval_pderiv_Fp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (x : Fin n → ℝ) (q : JJ n d) (i : Fin n) (W : WIdx n d → ℝ) :
    eval W (pderiv (q, i) (Fp (d := d) a H x)) = pf x q * Tv a H i x W := by
  classical
  have hs : ∀ k, H k i = H i k := fun k => by
    have := congrFun (congrFun hH i) k; simpa [Matrix.transpose_apply] using this
  simp only [Fp, Tv, map_sum, map_add, Derivation.leibniz, pderiv_C, pderiv_Zp, smul_eq_mul,
    mul_zero, add_zero, map_mul, eval_C, eval_Zp, mul_ite, apply_ite (eval W), map_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ite_mul, zero_mul, zero_add]
  simp only [hs, mul_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib, mul_comm (a i)]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

lemma Tv_aff (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ)
    (W : WIdx n d → ℝ) :
    Tv a H i x W = a i + ∑ β : WIdx n d, (2 * H i β.2 * pf x β.1) * W β := by
  unfold Tv zv
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

lemma PP_Zp (i : Fin n) : PP 1 (fun x : Fin n → ℝ => Zp (d := d) x i) := by
  unfold Zp
  refine BstLean.Part78.PP.sum _ fun q _ => ?_
  have := (BstLean.Part78.PP.coef (ι := WIdx n d) (continuous_pf q)).mul
    (BstLean.Part78.PP.const (n := n) (d := 1) (X (q, i) : MvPolynomial (WIdx n d) ℝ) (by simp))
  simpa using this

lemma PP_C (c : ℝ) : PP (n := n) 0 (fun _ => (C c : MvPolynomial (WIdx n d) ℝ)) :=
  BstLean.Part78.PP.const _ (by simp)

lemma PP_Fp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) : PP 2 (Fp (d := d) a H) := by
  unfold Fp
  refine BstLean.Part78.PP.add (BstLean.Part78.PP.sum _ fun i _ => ?_) (BstLean.Part78.PP.sum _ fun i _ => BstLean.Part78.PP.sum _ fun j _ => ?_)
  · exact (((PP_C (a i)).mul (PP_Zp (d := d) i))).mono (by norm_num)
  · exact ((((PP_C (H i j)).mul (PP_Zp (d := d) i))).mul (PP_Zp (d := d) j)).mono (by norm_num)

lemma PP_Tp (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : PP 1 (Tp (d := d) a H i) := by
  unfold Tp
  refine BstLean.Part78.PP.add ((PP_C (a i)).mono (by norm_num)) ?_
  have := (PP_C (n := n) 2).mul (BstLean.Part78.PP.sum Finset.univ fun j _ => (PP_C (H i j)).mul (PP_Zp (d := d) j))
  exact this.mono (by norm_num)

/-! ### The mean, `Q_x`, and `V` as polynomials -/

/-- `E_y F_y` as a polynomial in `W`. -/
noncomputable def Fbar (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (WIdx n d) ℝ := Classical.choose ((PP_Fp (d := d) a H).int hn)

lemma Fbar_deg (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    (Fbar (d := d) hn a H).totalDegree ≤ 2 := (Classical.choose_spec ((PP_Fp (d := d) a H).int hn)).1

lemma Fbar_eval (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n d → ℝ) :
    eval W (Fbar (d := d) hn a H) = ∫ x, FG a H W x ∂uniformSphere n := by
  have := (Classical.choose_spec ((PP_Fp (d := d) a H).int hn)).2.1 W
  unfold Fbar
  simpa only [eval_Fp] using this

/-- `Q_x = F_x − E_y F_y`. -/
noncomputable def Qp (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial (WIdx n d) ℝ := Fp (d := d) a H x - Fbar (d := d) hn a H

lemma PP_Qp (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) : PP 2 (Qp (d := d) hn a H) :=
  (PP_Fp (d := d) a H).sub (BstLean.Part78.PP.const _ (Fbar_deg hn a H))

lemma Qp_mean (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n d → ℝ) :
    ∫ x, eval W (Qp (d := d) hn a H x) ∂uniformSphere n = 0 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have he : (fun x => eval W (Qp (d := d) hn a H x)) = fun x => FG a H W x - eval W (Fbar (d := d) hn a H) := by
    funext x; simp [Qp]
  have hi : Integrable (fun x => FG a H W x) (uniformSphere n) := by
    have := (PP_Fp (d := d) a H).int_x hn W
    simpa only [eval_Fp] using this
  rw [he, integral_sub hi (integrable_const _), integral_const, Fbar_eval]
  simp

/-- `V` as a polynomial in `W`. -/
noncomputable def PVp (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (WIdx n d) ℝ := Classical.choose ((PP_Qp (d := d) hn a H).sq.int hn)

lemma PVp_eval (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n d → ℝ) :
    eval W (PVp (d := d) hn a H) = VG a H W := by
  have := (Classical.choose_spec ((PP_Qp (d := d) hn a H).sq.int hn)).2.1 W
  rw [PVp, this]
  simp [VG, varU, Qp, Fbar_eval]

lemma PVp_eval' (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n d → ℝ) :
    VG a H W = ∫ x, (eval W (Qp (d := d) hn a H x)) ^ 2 ∂uniformSphere n := by
  have := (Classical.choose_spec ((PP_Qp (d := d) hn a H).sq.int hn)).2.1 W
  rw [← PVp_eval hn, PVp, this]
  simp

/-- The gradient of `V`. -/
lemma PVp_grad (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (q : JJ n d) (i : Fin n) (W : WIdx n d → ℝ) :
    eval W (pderiv (q, i) (PVp (d := d) hn a H)) =
      2 * ∫ x, (eval W (Qp (d := d) hn a H x) * Tv a H i x W) * pf x q ∂uniformSphere n := by
  have h := (Classical.choose_spec ((PP_Qp (d := d) hn a H).sq.int hn)).2.2 (q, i) W
  rw [PVp, h]
  set cW := eval W (pderiv (q, i) (Fbar (d := d) hn a H)) with hcW
  have e : (fun x => eval W (pderiv (q, i) (Qp (d := d) hn a H x ^ 2))) = fun x =>
      2 * ((eval W (Qp (d := d) hn a H x) * Tv a H i x W) * pf x q) - (2 * cW) * eval W (Qp (d := d) hn a H x) := by
    funext x
    have h1 : eval W (pderiv (q, i) (Qp (d := d) hn a H x)) = pf x q * Tv a H i x W - cW := by
      simp only [Qp, map_sub, eval_pderiv_Fp a H hH, hcW]
    rw [pow_two, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, h1]
    ring
  have i1 : Integrable (fun x => 2 * ((eval W (Qp (d := d) hn a H x) * Tv a H i x W) * pf x q))
      (uniformSphere n) := by
    refine (sphere_cont_integrable78 hn ?_).const_mul _
    refine (((PP_Qp (d := d) hn a H).cont_x W).mul ?_).mul (continuous_pf q)
    have := (PP_Tp (d := d) a H i).cont_x W
    simpa only [eval_Tp] using this
  have i2 : Integrable (fun x => (2 * cW) * eval W (Qp (d := d) hn a H x)) (uniformSphere n) :=
    ((PP_Qp (d := d) hn a H).int_x hn W).const_mul _
  rw [e, integral_sub i1 i2, integral_const_mul, integral_const_mul, Qp_mean]
  ring


end BstLean.Part81.VarP
