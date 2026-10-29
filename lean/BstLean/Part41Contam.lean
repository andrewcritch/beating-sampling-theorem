import BstLean.Part41Defs
import BstLean.Part33Moments
import BstLean.Part36Index

/-!
# Part 41, wave 1: the contamination bound (Lemma `LC` (a), (c) and Lemma `LF` (iii))

Paper: Lemmas `LC` and `LF` (iii) of `proofs/option-m/41-arbitrary-degree.tex`, with the crude constant
`Ψ_m(s) ≤ (d+1)^m` (Bessel). Specification: `delegations/answers/p41-spec-opus.md`, flag 3.
Do not use `native_decide`.

Route (heavy). Expand `w_S` in Wiener chaoses of `Z`: by parity, the chaos-`m` part vanishes for `m < s`
(Lemma `LC` (a)), the chaos-`s` part is `q_S[b_s]` (Lemma `LC` (b)), and the chaos-`m` part is
`⟨E_x[X_m(x) x^S]/√m_S, :Z^{⊗m}:⟩` (Lemma `LC` (c)). So `w_S − q_S` is the sum of the chaoses `m > s`.
Chaos orthogonality gives `E (w_S − q_S)² = Σ_{m>s} m! ‖E_x[X_m x^S]‖² / m_S`; Cauchy–Schwarz over `l`,
`0 ≤ ‖φ‖^{2l} ≤ (d+1)^l`, the Bessel bound `Σ_S Σ_p (E x^{Σp+1_S})²/m_S ≤ E‖φ‖^{2m} ≤ (d+1)^m`,
`α_s = n^{−1} n^{−(m−1−s)} α_m`, and `frob_trL_le`.
A direct route that avoids Wiener chaos: `w_S − q_S` is an explicit polynomial in `Z`; compute its second
moment with the Gaussian moments of Part 29 and bound it term by term.
-/

namespace BstLean.Part41

open MeasureTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD rhoD)

variable {n d : ℕ}

private lemma sphere_cont_integrable (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (BstLean.Part29.uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma gaussian_eval_integrable {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) :
    Integrable (fun z => MvPolynomial.eval z p) (stdGauss ι) := by
  classical
  rw [p.as_sum]
  simp only [map_sum, MvPolynomial.eval_monomial]
  apply integrable_finsetSum
  intro e he
  have hprod (z : ι → ℝ) : e.prod (fun i a => z i ^ a) = ∏ i, z i ^ e i :=
    Finsupp.prod_fintype _ _ (by simp)
  simp_rw [hprod]
  exact (Integrable.fintype_prod (fun i =>
    ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet
      (X := fun x : ℝ => x) (by simp) (e i))).const_mul _

private abbrev JointPoly (n d : ℕ) :=
  MvPolynomial (CoefIdxD n d) C((Fin n → ℝ), ℝ)

private noncomputable def jointEval (p : JointPoly n d)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z p

private lemma joint_integral_polynomial (hn : 1 ≤ n) (p : JointPoly n d) :
    ∃ q : MvPolynomial (CoefIdxD n d) ℝ, ∀ Z,
      (∫ x, jointEval p Z x ∂BstLean.Part29.uniformSphere n) = MvPolynomial.eval Z q := by
  classical
  refine ⟨∑ e ∈ p.support, MvPolynomial.monomial e
    (∫ x, p.coeff e x ∂BstLean.Part29.uniformSphere n), ?_⟩
  intro Z
  have hE (x) : jointEval p Z x =
      ∑ e ∈ p.support, p.coeff e x * e.prod (fun i a => Z i ^ a) := by
    conv_lhs => unfold jointEval; rw [p.as_sum]
    simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
      Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply]
  simp_rw [hE]
  rw [integral_finsetSum _ (fun e _ =>
    (sphere_cont_integrable hn (p.coeff e).continuous).mul_const _)]
  simp only [integral_mul_const, map_sum, MvPolynomial.eval_monomial]

private lemma continuous_mono (s : Multiset (Fin n)) :
    Continuous (fun x : Fin n → ℝ => BstLean.Part36.monoVal x s) := by
  exact continuous_multiset_prod s (fun i _ => continuous_apply i)

private noncomputable def mapJoint (a : Fin n) : JointPoly n d :=
  ∑ i ∈ Finset.range (d + 1), ∑ β : Sym (Fin n) i,
    (if h : i < d + 1 then MvPolynomial.X ⟨⟨i, h⟩, (β, a)⟩ else 0) *
      MvPolynomial.C ⟨fun x => BstLean.Part36.monoVal x β.1, continuous_mono β.1⟩

private lemma mapJoint_eval (a : Fin n) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (mapJoint a) Z x = BstLean.Part36.mapMD Z x a := by
  classical
  unfold mapJoint jointEval BstLean.Part36.mapMD BstLean.Part36.coefD
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h : i < d + 1 := Finset.mem_range.mp hi
  simp [h]

private noncomputable def pJoint (k : ℕ) (T : Tens n) : JointPoly n d :=
  ∑ j ∈ Finset.Icc 1 k, (∑ w : Fin j → Fin n,
    MvPolynomial.C (ContinuousMap.const _ (T j w)) * ∏ t, mapJoint (w t)) *
      MvPolynomial.C (ContinuousMap.const _ ((Real.sqrt (BstLean.Part36.DD n d) ^ j)⁻¹))

private lemma pJoint_eval (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (pJoint (d := d) k T) Z x = Pcal k T Z x := by
  classical
  simp [pJoint, jointEval, Pcal, uJ, contr, div_eq_mul_inv,
    show ∀ a, MvPolynomial.eval₂
      ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z (mapJoint a) =
        BstLean.Part36.mapMD Z x a from fun a => mapJoint_eval a Z x]

private lemma wS_polynomial (hn : 1 ≤ n) (k : ℕ) (T : Tens n) (S : Finset (Fin n)) :
    ∃ p : MvPolynomial (CoefIdxD n d) ℝ, ∀ Z, wS k T S Z = MvPolynomial.eval Z p := by
  classical
  let c : C((Fin n → ℝ), ℝ) := ⟨fun x => ∏ a ∈ S, x a, by fun_prop⟩
  obtain ⟨q, hq⟩ := joint_integral_polynomial hn
    (pJoint (d := d) k T * MvPolynomial.C c)
  refine ⟨q * MvPolynomial.C (Real.sqrt (BstLean.Part36.rhoD n S.card)), ?_⟩
  intro Z
  have he (x) : jointEval (pJoint (d := d) k T * MvPolynomial.C c) Z x =
      Pcal k T Z x * ∏ a ∈ S, x a := by
    unfold jointEval
    rw [map_mul, MvPolynomial.eval₂Hom_C]
    change jointEval (pJoint (d := d) k T) Z x * c x = _
    rw [pJoint_eval]
    rfl
  specialize hq Z
  simp_rw [he] at hq
  change (∫ x, Pcal k T Z x * ∏ a ∈ S, x a ∂BstLean.Part29.uniformSphere n) *
    Real.sqrt (BstLean.Part36.rhoD n S.card) = _
  rw [hq]
  simp

private lemma qS_polynomial {s : ℕ} (b : (Fin s → Fin n) → ℝ) (S : Finset (Fin n)) :
    ∃ p : MvPolynomial (CoefIdxD n d) ℝ, ∀ Z, qS b S Z = MvPolynomial.eval Z p := by
  classical
  let c (β : Finset (Fin n)) (a : Fin n) : MvPolynomial (CoefIdxD n d) ℝ :=
    if h : β.card = d then MvPolynomial.X ⟨Fin.last d, (⟨β.val, h⟩, a)⟩ else 0
  have hc (β : Finset (Fin n)) (a : Fin n) (Z : CoefIdxD n d → ℝ) :
      MvPolynomial.eval Z (c β a) = colP Z β a := by
    unfold c colP
    split_ifs <;> simp
  refine ⟨MvPolynomial.C ((Real.sqrt (BstLean.Part36.rhoD n (s * d)))⁻¹) *
    ∑ π ∈ parts d s S, ∑ w : Fin s → Fin n, MvPolynomial.C (b w) * ∏ t, c (π t) (w t), ?_⟩
  intro Z
  simp [qS, contr, hc]

private lemma Halpha_integrable (hn : 1 ≤ n) (k : ℕ) (T : Tens n) :
    Integrable (Halpha (d := d) k T) (stdGauss (CoefIdxD n d)) := by
  classical
  unfold Halpha
  apply integrable_finsetSum
  intro s hs
  apply Integrable.div_const
  apply integrable_finsetSum
  intro S hS
  obtain ⟨p, hp⟩ := wS_polynomial (d := d) hn k T S
  obtain ⟨q, hq⟩ := qS_polynomial (d := d) (bEff n d k T s) S
  have hh := gaussian_eval_integrable ((p - q) ^ 2)
  simpa only [MvPolynomial.eval_pow, MvPolynomial.eval_sub, ← hp, ← hq] using hh

/-! Arbitrary-order Gaussian integration by parts, Wick orthogonality, and norm bounds. -/

private lemma gaussMom_step (a : ℕ) :
    BstLean.Part29.gaussMom (a + 2) = (a + 1 : ℝ) * BstLean.Part29.gaussMom a := by
  unfold BstLean.Part29.gaussMom
  have h : Even (a + 2) ↔ Even a := by simp [Nat.even_add]
  simp only [h]
  split_ifs with ha
  · rw [show a + 2 - 1 = a + 1 by omega, Nat.doubleFactorial_add_one]
    push_cast
    rfl
  · ring

private lemma gaussMom_stein (a : ℕ) :
    BstLean.Part29.gaussMom (a + 1) = (a : ℝ) * BstLean.Part29.gaussMom (a - 1) := by
  cases a with
  | zero => norm_num [BstLean.Part29.gaussMom]
  | succ a => simpa [Nat.succ_eq_add_one] using gaussMom_step a

private lemma gaussian_power_stein {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (i : ι) :
    (∫ Z, Z i * ∏ j, Z j ^ a j ∂stdGauss ι) =
      (a i : ℝ) * ∫ Z, ∏ j, Z j ^ (a j - if j = i then 1 else 0) ∂stdGauss ι := by
  classical
  have he (Z : ι → ℝ) : Z i * (∏ j, Z j ^ a j) =
      ∏ j, Z j ^ (a j + if j = i then 1 else 0) := by
    simp only [pow_add, Finset.prod_mul_distrib]
    simp [mul_comm, Finset.prod_ite_eq']
  simp_rw [he]
  have hmom (b : ι → ℕ) :
      (∫ Z, ∏ j, Z j ^ b j ∂stdGauss ι) = ∏ j, BstLean.Part29.gaussMom (b j) := by
    unfold stdGauss
    rw [integral_fintype_prod_eq_prod (f := fun j (x : ℝ) => x ^ b j)]
    simp_rw [BstLean.Part29.gaussMom_eq]
  rw [hmom, hmom, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true, gaussMom_stein]
  have hprod :
      (∏ j ∈ Finset.univ.erase i,
        BstLean.Part29.gaussMom (a j + if j = i then 1 else 0)) =
      ∏ j ∈ Finset.univ.erase i,
        BstLean.Part29.gaussMom (a j - if j = i then 1 else 0) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Finset.ne_of_mem_erase hj]
  rw [hprod]
  ring

private lemma gaussian_polynomial_stein {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (i : ι) :
    (∫ Z, Z i * MvPolynomial.eval Z p ∂stdGauss ι) =
      ∫ Z, MvPolynomial.eval Z (MvPolynomial.pderiv i p) ∂stdGauss ι := by
  classical
  have hmono (e : ι →₀ ℕ) (c : ℝ) :
      (∫ Z, Z i * MvPolynomial.eval Z (MvPolynomial.monomial e c) ∂stdGauss ι) =
        ∫ Z, MvPolynomial.eval Z (MvPolynomial.pderiv i (MvPolynomial.monomial e c))
          ∂stdGauss ι := by
    have he (e : ι →₀ ℕ) (Z : ι → ℝ) :
        e.prod (fun j a => Z j ^ a) = ∏ j, Z j ^ e j :=
      Finsupp.prod_fintype _ _ (by simp)
    simp only [MvPolynomial.pderiv_monomial, MvPolynomial.eval_monomial, he,
      Finsupp.tsub_apply, Finsupp.single_apply]
    simp_rw [show ∀ Z : ι → ℝ, Z i * (c * ∏ j, Z j ^ e j) =
      c * (Z i * ∏ j, Z j ^ e j) by intro Z; ring]
    rw [integral_const_mul, gaussian_power_stein, integral_const_mul]
    simp only [eq_comm, mul_assoc]
  have hi (q : MvPolynomial ι ℝ) :
      Integrable (fun Z => Z i * MvPolynomial.eval Z q) (stdGauss ι) := by
    have hh := gaussian_eval_integrable (MvPolynomial.X i * q)
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hh
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun e _ => hi _),
    integral_finsetSum _ (fun e _ => gaussian_eval_integrable _)]
  exact Finset.sum_congr rfl (fun e _ => hmono e (p.coeff e))

private noncomputable def gaussianExpectation {ι : Type*} [Fintype ι] :
    MvPolynomial ι ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ Z, MvPolynomial.eval Z p ∂stdGauss ι
  map_add' p q := by
    simp only [MvPolynomial.eval_add]
    exact integral_add (gaussian_eval_integrable p) (gaussian_eval_integrable q)
  map_smul' c p := by
    simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, smul_eq_mul]
    exact integral_const_mul _ _

private lemma gaussianExpectation_X_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (p : MvPolynomial ι ℝ) :
    gaussianExpectation (MvPolynomial.X i * p) =
      gaussianExpectation (MvPolynomial.pderiv i p) := by
  simpa only [gaussianExpectation, LinearMap.coe_mk, AddHom.coe_mk,
    MvPolynomial.eval_mul, MvPolynomial.eval_X] using gaussian_polynomial_stein p i

private noncomputable def wickRaise {ι : Type*} [DecidableEq ι]
    (i : ι) (p : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  MvPolynomial.X i * p - MvPolynomial.pderiv i p

private lemma wickRaise_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (p q : MvPolynomial ι ℝ) :
    gaussianExpectation (wickRaise i p * q) =
      gaussianExpectation (p * MvPolynomial.pderiv i q) := by
  have h := gaussianExpectation_X_mul i (p * q)
  rw [MvPolynomial.pderiv_mul, map_add] at h
  unfold wickRaise
  rw [sub_mul, map_sub, mul_assoc, h]
  ring

private noncomputable def wickWord {ι : Type*} [DecidableEq ι] :
    List ι → MvPolynomial ι ℝ
  | [] => 1
  | i :: w => wickRaise i (wickWord w)

private noncomputable def wordDeriv {ι : Type*} [DecidableEq ι] :
    List ι → MvPolynomial ι ℝ → MvPolynomial ι ℝ
  | [], p => p
  | i :: w, p => wordDeriv w (MvPolynomial.pderiv i p)

private lemma wickWord_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : List ι) (p : MvPolynomial ι ℝ) :
    gaussianExpectation (wickWord w * p) = gaussianExpectation (wordDeriv w p) := by
  induction w generalizing p with
  | nil => simp [wickWord, wordDeriv]
  | cons i w ih =>
    rw [wickWord, wickRaise_adjoint, ih]
    rfl

private lemma pderiv_degree {ι : Type*} [DecidableEq ι]
    (i : ι) (p : MvPolynomial ι ℝ) :
    (MvPolynomial.pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro e he
  have hc : p.coeff (e + Finsupp.single i 1) ≠ 0 := by
    have hh := MvPolynomial.mem_support_iff.mp he
    rw [MvPolynomial.coeff_pderiv] at hh
    exact (mul_ne_zero_iff.mp hh).1
  have hh := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  have hs : (e + Finsupp.single i 1).sum (fun _ a => a) = e.sum (fun _ a => a) + 1 := by
    simp [Finsupp.sum_add_index']
  rw [hs] at hh
  exact Nat.le_sub_one_of_lt hh

private lemma wordDeriv_zero {ι : Type*} [DecidableEq ι] (w : List ι) :
    wordDeriv w (0 : MvPolynomial ι ℝ) = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa [wordDeriv] using ih

private lemma wordDeriv_eq_zero_of_degree_lt {ι : Type*} [DecidableEq ι]
    (w : List ι) (p : MvPolynomial ι ℝ) (hp : p.totalDegree < w.length) :
    wordDeriv w p = 0 := by
  induction w generalizing p with
  | nil => simp at hp
  | cons i w ih =>
    change wordDeriv w (MvPolynomial.pderiv i p) = 0
    by_cases hz : p.totalDegree = 0
    · have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz
      rw [hc, MvPolynomial.pderiv_C]
      exact wordDeriv_zero w
    · apply ih
      have hd := pderiv_degree i p
      simp only [List.length_cons] at hp
      omega

private lemma wickWord_degree {ι : Type*} [DecidableEq ι] (w : List ι) :
    (wickWord w).totalDegree ≤ w.length := by
  induction w with
  | nil => simp [wickWord]
  | cons i w ih =>
    unfold wickWord wickRaise
    have hm := MvPolynomial.totalDegree_mul (MvPolynomial.X i) (wickWord w)
    have hd := pderiv_degree i (wickWord w)
    have hs := MvPolynomial.totalDegree_sub
      (MvPolynomial.X i * wickWord w) (MvPolynomial.pderiv i (wickWord w))
    simp only [MvPolynomial.totalDegree_X] at hm
    simp only [List.length_cons]
    omega

private lemma wickWord_orthogonal_low_degree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : List ι) (p : MvPolynomial ι ℝ) (hp : p.totalDegree < w.length) :
    gaussianExpectation (wickWord w * p) = 0 := by
  rw [wickWord_adjoint, wordDeriv_eq_zero_of_degree_lt w p hp, map_zero]

private lemma wickWord_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : List ι) (h : w.length ≠ v.length) :
    gaussianExpectation (wickWord w * wickWord v) = 0 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [mul_comm]
    exact wickWord_orthogonal_low_degree v (wickWord w) ((wickWord_degree w).trans_lt hlt)
  · exact wickWord_orthogonal_low_degree w (wickWord v) ((wickWord_degree v).trans_lt hgt)

private noncomputable def plainWord {ι : Type*} : List ι → MvPolynomial ι ℝ
  | [] => 1
  | i :: w => MvPolynomial.X i * plainWord w

private lemma wickWord_remainder_degree {ι : Type*} [DecidableEq ι] (w : List ι) :
    (plainWord w - wickWord w).totalDegree ≤ w.length - 1 := by
  induction w with
  | nil => simp [plainWord, wickWord]
  | cons i w ih =>
    cases w with
    | nil => simp [plainWord, wickWord, wickRaise]
    | cons j w =>
      have he : plainWord (i :: j :: w) - wickWord (i :: j :: w) =
          MvPolynomial.X i * (plainWord (j :: w) - wickWord (j :: w)) +
            MvPolynomial.pderiv i (wickWord (j :: w)) := by
        simp only [plainWord, wickWord, wickRaise]
        ring
      rw [he]
      have hm := MvPolynomial.totalDegree_mul (MvPolynomial.X i)
        (plainWord (j :: w) - wickWord (j :: w))
      have hd := pderiv_degree i (wickWord (j :: w))
      have hw := wickWord_degree (j :: w)
      have ha := MvPolynomial.totalDegree_add
        (MvPolynomial.X i * (plainWord (j :: w) - wickWord (j :: w)))
        (MvPolynomial.pderiv i (wickWord (j :: w)))
      simp only [MvPolynomial.totalDegree_X, List.length_cons] at *
      omega

private lemma wickWord_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : List ι) (h : w.length = v.length) :
    gaussianExpectation (wickWord w * wickWord v) =
      gaussianExpectation (wordDeriv w (plainWord v)) := by
  by_cases hv : v = []
  · subst v
    have hw : w = [] := List.length_eq_zero_iff.mp (by simpa using h)
    subst w
    simp [plainWord, wickWord, wordDeriv]
  · have hd := wickWord_remainder_degree v
    have hz := wickWord_orthogonal_low_degree w (plainWord v - wickWord v)
      (by have hl := List.length_pos_iff.mpr hv; omega)
    rw [mul_sub, map_sub] at hz
    rw [← wickWord_adjoint]
    linarith

private lemma coeff_nonneg_plainWord {ι : Type*} [DecidableEq ι]
    (w : List ι) (e : ι →₀ ℕ) : 0 ≤ (plainWord w).coeff e := by
  induction w generalizing e with
  | nil => simp only [plainWord, MvPolynomial.coeff_one]; split_ifs <;> norm_num
  | cons i w ih =>
    rw [plainWord, MvPolynomial.coeff_mul]
    apply Finset.sum_nonneg
    intro a ha
    apply mul_nonneg _ (ih a.2)
    simp only [MvPolynomial.coeff_X]
    split_ifs <;> norm_num

private lemma coeff_nonneg_wordDeriv {ι : Type*} [DecidableEq ι]
    (w : List ι) (p : MvPolynomial ι ℝ) (hp : ∀ e, 0 ≤ p.coeff e) :
    ∀ e, 0 ≤ (wordDeriv w p).coeff e := by
  induction w generalizing p with
  | nil => exact hp
  | cons i w ih =>
    apply ih
    intro e
    rw [MvPolynomial.coeff_pderiv]
    exact mul_nonneg (hp _) (by positivity)

private lemma gaussianExpectation_nonneg_coeff {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (hp : ∀ e, 0 ≤ p.coeff e) :
    0 ≤ gaussianExpectation p := by
  classical
  change 0 ≤ ∫ Z, MvPolynomial.eval Z p ∂stdGauss ι
  conv_rhs => rw [p.as_sum]
  simp only [map_sum]
  rw [integral_finsetSum _ (fun e _ => gaussian_eval_integrable _)]
  apply Finset.sum_nonneg
  intro e he
  simp only [MvPolynomial.eval_monomial]
  have hprod (Z : ι → ℝ) : e.prod (fun i a => Z i ^ a) = ∏ i, Z i ^ e i :=
    Finsupp.prod_fintype _ _ (by simp)
  simp_rw [hprod]
  rw [integral_const_mul]
  apply mul_nonneg (hp _)
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (f := fun i (x : ℝ) => x ^ e i)]
  simp_rw [BstLean.Part29.gaussMom_eq]
  apply Finset.prod_nonneg
  intro i hi
  unfold BstLean.Part29.gaussMom
  split_ifs <;> positivity

private lemma wickWord_covariance_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : List ι) : 0 ≤ gaussianExpectation (wickWord w * wickWord v) := by
  by_cases h : w.length = v.length
  · rw [wickWord_covariance w v h]
    exact gaussianExpectation_nonneg_coeff _
      (coeff_nonneg_wordDeriv w (plainWord v) (coeff_nonneg_plainWord v))
  · rw [wickWord_orthogonal w v h]

private lemma wordDeriv_sum {ι κ : Type*} [DecidableEq ι]
    (w : List ι) (s : Finset κ) (p : κ → MvPolynomial ι ℝ) :
    wordDeriv w (∑ a ∈ s, p a) = ∑ a ∈ s, wordDeriv w (p a) := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih => simp only [wordDeriv, map_sum, ih]

private lemma wordDeriv_C_mul {ι : Type*} [DecidableEq ι]
    (w : List ι) (c : ℝ) (p : MvPolynomial ι ℝ) :
    wordDeriv w (MvPolynomial.C c * p) = MvPolynomial.C c * wordDeriv w p := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih => simp only [wordDeriv, MvPolynomial.pderiv_C_mul, ih]

private lemma plainWord_ofFn {ι : Type*} {m : ℕ} (w : Fin m → ι) :
    plainWord (List.ofFn w) = ∏ t, (MvPolynomial.X (w t) : MvPolynomial ι ℝ) := by
  induction m with
  | zero => simp [plainWord]
  | succ m ih => simp [List.ofFn_succ, plainWord, Fin.prod_univ_succ, ih]

private lemma wordDeriv_sumX_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (w : List ι) :
    wordDeriv w ((∑ i : ι, (MvPolynomial.X i : MvPolynomial ι ℝ)) ^ w.length) =
      MvPolynomial.C (w.length.factorial : ℝ) := by
  induction w with
  | nil => simp [wordDeriv]
  | cons i w ih =>
    have hs : MvPolynomial.pderiv i (∑ j : ι, (MvPolynomial.X j : MvPolynomial ι ℝ)) = 1 := by
      simp [Pi.single_apply]
    simp only [wordDeriv, List.length_cons, MvPolynomial.pderiv_pow, hs,
      Nat.add_sub_cancel, mul_one]
    rw [← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ)]
    change wordDeriv w (MvPolynomial.C ((w.length + 1 : ℕ) : ℝ) *
      (∑ i : ι, (MvPolynomial.X i : MvPolynomial ι ℝ)) ^ w.length) = _
    rw [wordDeriv_C_mul, ih, ← map_mul]
    simp [Nat.factorial_succ, Nat.cast_mul]

private lemma gaussianExpectation_C {ι : Type*} [Fintype ι] (c : ℝ) :
    gaussianExpectation (MvPolynomial.C c : MvPolynomial ι ℝ) = c := by
  simp [gaussianExpectation]

private lemma gaussianExpectation_C_mul {ι : Type*} [Fintype ι]
    (c : ℝ) (p : MvPolynomial ι ℝ) :
    gaussianExpectation (MvPolynomial.C c * p) = c * gaussianExpectation p := by
  simpa only [MvPolynomial.smul_eq_C_mul, smul_eq_mul] using
    (gaussianExpectation (ι := ι)).map_smul c p

private lemma wickWord_covariance_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (w : Fin m → ι) :
    (∑ v : Fin m → ι, gaussianExpectation (wickWord (List.ofFn w) * wickWord (List.ofFn v))) =
      (m.factorial : ℝ) := by
  classical
  have hc (v : Fin m → ι) := wickWord_covariance (List.ofFn w) (List.ofFn v)
    (by simp only [List.length_ofFn])
  simp_rw [hc]
  rw [← map_sum, ← wordDeriv_sum]
  simp_rw [plainWord_ofFn]
  rw [← Fintype.sum_pow]
  have ht := wordDeriv_sumX_pow (List.ofFn w)
  simp only [List.length_ofFn] at ht
  rw [ht, gaussianExpectation_C]

private lemma wickTensor_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (A : (Fin m → ι) → ℝ) :
    gaussianExpectation
      ((∑ w : Fin m → ι, MvPolynomial.C (A w) * wickWord (List.ofFn w)) ^ 2) ≤
      (m.factorial : ℝ) * ∑ w, A w ^ 2 := by
  classical
  let C (w v : Fin m → ι) :=
    gaussianExpectation (wickWord (List.ofFn w) * wickWord (List.ofFn v))
  have hC (w v : Fin m → ι) : 0 ≤ C w v := wickWord_covariance_nonneg _ _
  have hrow (w : Fin m → ι) : ∑ v, C w v = (m.factorial : ℝ) := wickWord_covariance_row w
  have hsym (w v : Fin m → ι) : C w v = C v w := by dsimp [C]; rw [mul_comm]
  have hcol (v : Fin m → ι) : ∑ w, C w v = (m.factorial : ℝ) := by
    simp_rw [hsym]; exact hrow v
  have hex : gaussianExpectation
      ((∑ w : Fin m → ι, MvPolynomial.C (A w) * wickWord (List.ofFn w)) ^ 2) =
      ∑ w, ∑ v, A w * A v * C w v := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro w hw
    apply Finset.sum_congr rfl
    intro v hv
    have he : (MvPolynomial.C (A w) * wickWord (List.ofFn w)) *
        (MvPolynomial.C (A v) * wickWord (List.ofFn v)) =
        MvPolynomial.C (A w * A v) * (wickWord (List.ofFn w) * wickWord (List.ofFn v)) := by
      rw [map_mul]
      ring
    rw [mul_comm, he, gaussianExpectation_C_mul]
  rw [hex]
  calc
    _ ≤ ∑ w, ∑ v, ((A w ^ 2 + A v ^ 2) / 2) * C w v := by
      apply Finset.sum_le_sum
      intro w hw
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (A w - A v)]) (hC w v)
    _ = (∑ w, ∑ v, (A w ^ 2 * C w v + A v ^ 2 * C w v)) / 2 := by
      simp_rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = ((∑ w, A w ^ 2 * (m.factorial : ℝ)) +
        ∑ v, A v ^ 2 * (m.factorial : ℝ)) / 2 := by
      simp only [Finset.sum_add_distrib]
      congr 1
      congr 1
      · simp_rw [← Finset.mul_sum, hrow]
      · rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, hcol]
    _ = _ := by rw [← Finset.sum_mul]; ring

private noncomputable def wickTensor {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : (Fin m → ι) → ℝ) : MvPolynomial ι ℝ :=
  ∑ w : Fin m → ι, MvPolynomial.C (A w) * wickWord (List.ofFn w)

private lemma wickTensor_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m r : ℕ} (A : (Fin m → ι) → ℝ) (B : (Fin r → ι) → ℝ) (h : m ≠ r) :
    gaussianExpectation (wickTensor A * wickTensor B) = 0 := by
  classical
  unfold wickTensor
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro v hv
  apply Finset.sum_eq_zero
  intro w hw
  have he : (MvPolynomial.C (A w) * wickWord (List.ofFn w)) *
      (MvPolynomial.C (B v) * wickWord (List.ofFn v)) =
      MvPolynomial.C (A w * B v) * (wickWord (List.ofFn w) * wickWord (List.ofFn v)) := by
    rw [map_mul]
    ring
  rw [he, gaussianExpectation_C_mul,
    wickWord_orthogonal _ _ (by simpa only [List.length_ofFn] using h), mul_zero]

set_option maxHeartbeats 1000000 in
private lemma wickTensor_sum_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ℕ) (A : (m : ℕ) → (Fin m → ι) → ℝ) :
    gaussianExpectation ((∑ m ∈ s, wickTensor (A m)) ^ 2) ≤
      ∑ m ∈ s, (m.factorial : ℝ) * frob (A m) := by
  classical
  have he : gaussianExpectation ((∑ m ∈ s, wickTensor (A m)) ^ 2) =
      ∑ m ∈ s, gaussianExpectation (wickTensor (A m) ^ 2) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_eq_single m
    · intro r hr hrm
      exact wickTensor_orthogonal (A r) (A m) hrm
    · intro hn
      exact (hn hm).elim
  rw [he]
  exact Finset.sum_le_sum (fun m hm => wickTensor_sq_le (A m))

private lemma contamination_of_wick_expansion (hn : 1 ≤ n) (k : ℕ) (T : Tens n)
    (A : ℕ → Finset (Fin n) → (m : ℕ) → (Fin m → CoefIdxD n d) → ℝ)
    (hA : ∀ s ∈ Finset.Icc 1 k,
      ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d), ∀ Z,
        wS k T S Z - qS (bEff n d k T s) S Z =
          MvPolynomial.eval Z (∑ m ∈ Finset.Icc (s + 1) k, wickTensor (A s S m))) :
    (∫ Z, Halpha k T Z ∂stdGauss (CoefIdxD n d)) ≤
      ∑ s ∈ Finset.Icc 1 k,
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d),
          ∑ m ∈ Finset.Icc (s + 1) k, (m.factorial : ℝ) * frob (A s S m)) /
            (n : ℝ) ^ (k - s) := by
  classical
  have hi (s : ℕ) (S : Finset (Fin n)) :
      Integrable (fun Z : CoefIdxD n d → ℝ =>
        (wS k T S Z - qS (bEff n d k T s) S Z) ^ 2) (stdGauss (CoefIdxD n d)) := by
    obtain ⟨p, hp⟩ := wS_polynomial (d := d) hn k T S
    obtain ⟨q, hq⟩ := qS_polynomial (d := d) (bEff n d k T s) S
    have hh := gaussian_eval_integrable ((p - q) ^ 2)
    simpa only [MvPolynomial.eval_pow, MvPolynomial.eval_sub, ← hp, ← hq] using hh
  unfold Halpha
  rw [integral_finsetSum _ (fun s hs =>
    (integrable_finsetSum _ (fun S hS => hi s S)).div_const _)]
  apply Finset.sum_le_sum
  intro s hs
  rw [integral_div, integral_finsetSum _ (fun S hS => hi s S)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro S hS
  have he (Z : CoefIdxD n d → ℝ) :
      (wS k T S Z - qS (bEff n d k T s) S Z) ^ 2 =
        MvPolynomial.eval Z ((∑ m ∈ Finset.Icc (s + 1) k, wickTensor (A s S m)) ^ 2) := by
    rw [hA s hs S hS Z, MvPolynomial.eval_pow]
  simp_rw [he]
  exact wickTensor_sum_sq_le (Finset.Icc (s + 1) k) (A s S)

/-! Sphere monomial energy bounds. The weighted Bessel estimate avoids a separate sign argument. -/

private lemma enum_exists {ι : Type*} {i : ℕ} (β : Sym ι i) :
    ∃ w : Fin i → ι, Finset.univ.val.map w = β.val := by
  have enum (b : Multiset ι) : ∃ (r : ℕ) (w : Fin r → ι),
      r = b.card ∧ Finset.univ.val.map w = b := by
    induction b using Quot.inductionOn with
    | h a => exact ⟨a.length, a.get, rfl, by simp [Fin.univ_val_map]⟩
  obtain ⟨r, w, hr, hw⟩ := enum β.val
  have hri : r = i := hr.trans β.property
  clear hr
  subst r
  exact ⟨w, hw⟩

private noncomputable def enumSym {ι : Type*} {i : ℕ} (β : Sym ι i) : Fin i → ι :=
  Classical.choose (enum_exists β)

private lemma enumSym_spec {ι : Type*} {i : ℕ} (β : Sym ι i) :
    Finset.univ.val.map (enumSym β) = β.val := Classical.choose_spec (enum_exists β)

private lemma enumSym_injective {ι : Type*} {i : ℕ} :
    Function.Injective (enumSym : Sym ι i → Fin i → ι) := by
  intro β γ h
  apply Subtype.ext
  rw [← enumSym_spec β, ← enumSym_spec γ, h]

private lemma mono_enum {i : ℕ} (β : Sym (Fin n) i) (x : Fin n → ℝ) :
    BstLean.Part36.monoVal x β.val = ∏ t, x (enumSym β t) := by
  rw [BstLean.Part36.monoVal, ← enumSym_spec β, Multiset.map_map]
  rfl

private lemma phiSq_le (x : Fin n → ℝ) (hx : ∑ a, x a ^ 2 = 1) :
    phiSq d x ≤ (d : ℝ) + 1 := by
  classical
  have hlevel (i : ℕ) : (∑ β : Sym (Fin n) i, BstLean.Part36.monoVal x β.val ^ 2) ≤ 1 := by
    calc
      _ = ∑ β : Sym (Fin n) i, ∏ t, x (enumSym β t) ^ 2 := by
        apply Finset.sum_congr rfl
        intro β hβ
        rw [mono_enum, Finset.prod_pow]
      _ ≤ ∑ w : Fin i → Fin n, ∏ t, x (w t) ^ 2 := by
        calc
          _ = ∑ w ∈ Finset.univ.image (enumSym : Sym (Fin n) i → Fin i → Fin n),
              ∏ t, x (w t) ^ 2 := by
            rw [Finset.sum_image (fun β _ γ _ h => enumSym_injective h)]
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun w _ _ => Finset.prod_nonneg (fun t _ => sq_nonneg _))
      _ = ∏ t : Fin i, ∑ a : Fin n, x a ^ 2 :=
        (Fintype.prod_sum (fun (_ : Fin i) (a : Fin n) => x a ^ 2)).symm
      _ = 1 := by simp [hx]
  unfold phiSq phiM
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ i : Fin (d + 1), (1 : ℝ) := Finset.sum_le_sum (fun i _ => hlevel i.val)
    _ = (d : ℝ) + 1 := by simp


private lemma squarefree_moment (hn : 1 ≤ n) (S : Finset (Fin n)) :
    Integrable (fun x => ∏ a ∈ S, x a ^ 2) (uniformSphere n) ∧
    (∫ x, ∏ a ∈ S, x a ^ 2 ∂uniformSphere n) = 1 / rhoD n S.card := by
  classical
  have hm (x : Fin n → ℝ) : BstLean.Part36.monoVal x (S.val + S.val) =
      ∏ a ∈ S, x a ^ 2 := by
    simp only [BstLean.Part36.monoVal, Multiset.map_add, Multiset.prod_add]
    rw [← pow_two, Finset.prod_pow]
    rfl
  have hg : BstLean.Part36.gpm (S.val + S.val) = 1 := by
    unfold BstLean.Part36.gpm
    apply Finset.prod_eq_one
    intro a ha
    by_cases h : a ∈ S
    · have hc : S.val.count a = 1 := Multiset.count_eq_one_of_mem S.nodup h
      norm_num [Multiset.count_add, hc, BstLean.Part29.gaussMom]
    · have hc : S.val.count a = 0 := Multiset.count_eq_zero.mpr h
      norm_num [Multiset.count_add, hc, BstLean.Part29.gaussMom]
  have h := BstLean.Part36.sphere_multiset (uniformSphere n)
    (BstLean.Part33.uniformSphere_prod n (2 * S.card) hn) (S.val + S.val) (by simp; omega)
  simpa only [hm, hg, Multiset.card_add, Finset.card_val,
    show (S.card + S.card) / 2 = S.card by omega] using h

private lemma rhoD_pos_local (hn : 1 ≤ n) (i : ℕ) : 0 < rhoD n i := by
  unfold rhoD
  apply Finset.prod_pos
  intro t ht
  have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  positivity


private lemma mono_finset_orth (hn : 1 ≤ n) (S T : Finset (Fin n)) (hST : S ≠ T) :
    (∫ x, (∏ a ∈ S, x a) * (∏ a ∈ T, x a) ∂uniformSphere n) = 0 := by
  classical
  have h := (BstLean.Part36.sphere_multiset (uniformSphere n)
    (BstLean.Part33.uniformSphere_prod n (S.card + T.card) hn) (S.val + T.val) (by simp)).2
  have hex : ∃ a, (a ∈ S ∧ a ∉ T) ∨ (a ∈ T ∧ a ∉ S) := by
    by_contra hh
    push Not at hh
    apply hST
    ext a
    constructor
    · intro ha
      exact (hh a).1 ha
    · intro ha
      exact (hh a).2 ha
  obtain ⟨a, ha⟩ := hex
  have hc : (S.val + T.val).count a = 1 := by
    rcases ha with ha | ha
    · rw [Multiset.count_add, Multiset.count_eq_one_of_mem S.nodup ha.1,
        Multiset.count_eq_zero.mpr ha.2]
    · rw [Multiset.count_add, Multiset.count_eq_zero.mpr ha.2,
        Multiset.count_eq_one_of_mem T.nodup ha.1]
  have hz : BstLean.Part36.gpm (S.val + T.val) = 0 := by
    unfold BstLean.Part36.gpm
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    norm_num [hc, BstLean.Part29.gaussMom]
  simpa [BstLean.Part36.monoVal, Multiset.map_add, Multiset.prod_add, hz] using h


private theorem energy_bound {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} (P : Measure Ω) (φ : ι → Ω → ℝ) (w : ℝ)
    (hw : 0 < w)
    (hφ2 : ∀ s t, Integrable (fun ω => φ s ω * φ t ω) P)
    (horth : ∀ s t, s ≠ t → ∫ ω, φ s ω * φ t ω ∂P = 0)
    (hnorm : ∀ s, ∫ ω, φ s ω ^ 2 ∂P = w)
    (S : Finset ι) :
    ∀ h : Ω → ℝ, Integrable (fun ω => h ω ^ 2) P →
    (∀ s, Integrable (fun ω => h ω * φ s ω) P) →
    ∑ s ∈ S, (∫ ω, h ω * φ s ω ∂P) ^ 2 / w ≤ ∫ ω, h ω ^ 2 ∂P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro h hh2 hhφ
      simpa using integral_nonneg (fun ω => sq_nonneg (h ω))
  | @insert a S ha ih =>
      intro h hh2 hhφ
      let c := (∫ ω, h ω * φ a ω ∂P) / w
      let r := fun ω => h ω - c * φ a ω
      have hpa : Integrable (fun ω => φ a ω ^ 2) P := by
        simpa only [pow_two] using hφ2 a a
      have hr2 : Integrable (fun ω => r ω ^ 2) P := by
        have := (hh2.sub ((hhφ a).const_mul (2*c))).add (hpa.const_mul (c^2))
        convert this using 1
        ext ω
        dsimp [r]
        ring
      have hrφ : ∀ s, Integrable (fun ω => r ω * φ s ω) P := by
        intro s
        convert (hhφ s).sub ((hφ2 a s).const_mul c) using 1
        ext ω
        dsimp [r]
        ring
      have hcov (s : ι) (hs : s ∈ S) :
          (∫ ω, r ω * φ s ω ∂P) = ∫ ω, h ω * φ s ω ∂P := by
        have has : a ≠ s := by intro e; exact ha (e ▸ hs)
        simp only [r, sub_mul, mul_assoc]
        rw [integral_sub (hhφ s) ((hφ2 a s).const_mul c), integral_const_mul,
          horth a s has]
        simp
      have he : (∫ ω, r ω ^ 2 ∂P) =
          (∫ ω, h ω ^ 2 ∂P) - (∫ ω, h ω * φ a ω ∂P)^2 / w := by
        have heq : (fun ω => r ω ^ 2) =
            (fun ω => (h ω ^ 2 - (2*c) * (h ω * φ a ω)) + c^2 * φ a ω ^ 2) := by
          funext ω
          dsimp [r]
          ring
        have hsub : Integrable (fun ω => h ω ^ 2 - (2*c) * (h ω * φ a ω)) P :=
          hh2.sub ((hhφ a).const_mul (2*c))
        rw [heq, integral_add hsub (hpa.const_mul (c^2)),
          integral_sub hh2 ((hhφ a).const_mul (2*c))]
        simp only [integral_const_mul, hnorm]
        dsimp [c]
        field_simp [ne_of_gt hw]
        ring
      have hb := ih r hr2 hrφ
      rw [he] at hb
      have hsum : (∑ s ∈ S, (∫ ω, r ω * φ s ω ∂P)^2 / w) =
          ∑ s ∈ S, (∫ ω, h ω * φ s ω ∂P)^2 / w := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hcov s hs]
      rw [hsum] at hb
      rw [Finset.sum_insert ha]
      linarith

private lemma sphere_weighted_bessel (hn : 1 ≤ n) (r : ℕ)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      (∫ x, f x * ∏ a ∈ S, x a ∂uniformSphere n) ^ 2 * rhoD n r) ≤
        ∫ x, f x ^ 2 ∂uniformSphere n := by
  classical
  let U := (Finset.univ : Finset (Fin n)).powersetCard r
  let φ : U → (Fin n → ℝ) → ℝ := fun S x =>
    (∏ a ∈ S.val, x a) * Real.sqrt (rhoD n r)
  have hr := rhoD_pos_local hn r
  have hc (S : U) : S.val.card = r := (Finset.mem_powersetCard.mp S.property).2
  have hφc (S : U) : Continuous (φ S) := by dsimp [φ]; fun_prop
  have hnorm (S : U) : (∫ x, φ S x ^ 2 ∂uniformSphere n) = 1 := by
    have he (x : Fin n → ℝ) : φ S x ^ 2 =
        rhoD n r * ∏ a ∈ S.val, x a ^ 2 := by
      simp only [φ, mul_pow, Real.sq_sqrt hr.le, Finset.prod_pow]
      ring
    simp_rw [he]
    rw [integral_const_mul, (squarefree_moment hn S.val).2, hc]
    exact mul_one_div_cancel hr.ne'
  have horth (S T : U) (hST : S ≠ T) :
      (∫ x, φ S x * φ T x ∂uniformSphere n) = 0 := by
    have he (x : Fin n → ℝ) : φ S x * φ T x =
        ((∏ a ∈ S.val, x a) * ∏ a ∈ T.val, x a) * rhoD n r := by
      dsimp [φ]
      calc
        _ = ((∏ a ∈ S.val, x a) * ∏ a ∈ T.val, x a) * (Real.sqrt (rhoD n r)) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hr.le]
    simp_rw [he]
    rw [integral_mul_const,
      mono_finset_orth hn S.val T.val (fun h => hST (Subtype.ext h)), zero_mul]
  have hb := energy_bound (uniformSphere n) φ 1 (by norm_num)
    (fun S T => sphere_cont_integrable hn ((hφc S).mul (hφc T))) horth hnorm
    Finset.univ f (sphere_cont_integrable hn (hf.pow 2))
    (fun S => sphere_cont_integrable hn (hf.mul (hφc S)))
  have hcov (S : U) : (∫ x, f x * φ S x ∂uniformSphere n) =
      (∫ x, f x * ∏ a ∈ S.val, x a ∂uniformSphere n) * Real.sqrt (rhoD n r) := by
    dsimp [φ]
    simp_rw [← mul_assoc]
    rw [integral_mul_const]
  simp only [hcov, div_one, mul_pow, Real.sq_sqrt hr.le] at hb
  rw [Finset.sum_coe_sort U (fun S =>
    (∫ x, f x * ∏ a ∈ S, x a ∂uniformSphere n) ^ 2 * rhoD n r)] at hb
  exact hb

private lemma phiSq_cont : Continuous (phiSq d : (Fin n → ℝ) → ℝ) := by
  classical
  unfold phiSq phiM
  exact continuous_finsetSum _ (fun p hp => (continuous_mono p.2.val).pow 2)

private lemma weighted_monomial_bessel (hn : 1 ≤ n) (r m l : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      ∑ p : Fin m → Mono n d,
        (∫ x, phiSq d x ^ l * (∏ t, phiM x (p t)) * ∏ a ∈ S, x a ∂uniformSphere n) ^ 2 *
          rhoD n r) ≤ ((d : ℝ) + 1) ^ (m + 2 * l) := by
  classical
  let F (p : Fin m → Mono n d) (x : Fin n → ℝ) := phiSq d x ^ l * ∏ t, phiM x (p t)
  have hFc (p : Fin m → Mono n d) : Continuous (F p) := by
    apply (phiSq_cont.pow l).mul
    exact continuous_finsetProd _ (fun t ht => continuous_mono (p t).2.val)
  have he (x : Fin n → ℝ) : (∑ p : Fin m → Mono n d, F p x ^ 2) = phiSq d x ^ (m + 2 * l) := by
    simp only [F, mul_pow, ← Finset.prod_pow, ← Finset.mul_sum]
    rw [← Fintype.prod_sum (fun (_ : Fin m) (p : Mono n d) => phiM x p ^ 2)]
    change (phiSq d x ^ l) ^ 2 * (∏ t : Fin m, phiSq d x) = _
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = ∑ p : Fin m → Mono n d, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        (∫ x, F p x * ∏ a ∈ S, x a ∂uniformSphere n) ^ 2 * rhoD n r := by
      rw [Finset.sum_comm]
    _ ≤ ∑ p : Fin m → Mono n d, ∫ x, F p x ^ 2 ∂uniformSphere n :=
      Finset.sum_le_sum (fun p hp => sphere_weighted_bessel hn r (F p) (hFc p))
    _ = ∫ x, phiSq d x ^ (m + 2 * l) ∂uniformSphere n := by
      rw [← integral_finsetSum (Finset.univ : Finset (Fin m → Mono n d))
        (f := fun p x => F p x ^ 2) (fun p hp => sphere_cont_integrable hn ((hFc p).pow 2))]
      simp_rw [he]
    _ ≤ ((d : ℝ) + 1) ^ (m + 2 * l) := by
      let := BstLean.Part29.uniformSphere_isProbability n hn
      have hi : Integrable (fun x : Fin n → ℝ => phiSq d x ^ (m + 2 * l)) (uniformSphere n) :=
        sphere_cont_integrable hn (phiSq_cont.pow (m + 2 * l))
      have hb : (∫ x, phiSq d x ^ (m + 2 * l) ∂uniformSphere n) ≤
          ∫ x, ((d : ℝ) + 1) ^ (m + 2 * l) ∂uniformSphere n := by
        apply integral_mono_ae hi (integrable_const _)
        filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
        exact pow_le_pow_left₀ (Finset.sum_nonneg (fun p hp => sq_nonneg _)) (phiSq_le x hx) _
      simpa using hb

/-! The Wick expansion of a symmetric plain product (list-indexed tensors). -/

section WickExp
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def wickL (m : ℕ) (G : List ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ w : Fin m → ι, MvPolynomial.C (G (List.ofFn w)) * wickWord (List.ofFn w)

noncomputable def plainL (m : ℕ) (G : List ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ w : Fin m → ι, MvPolynomial.C (G (List.ofFn w)) * plainWord (List.ofFn w)

def dblL {l : ℕ} (c : Fin l → ι) : List ι := (List.ofFn c).flatMap (fun a => [a, a])

noncomputable def traceL (l : ℕ) (G : List ι → ℝ) (u : List ι) : ℝ :=
  ∑ c : Fin l → ι, G (dblL c ++ u)


open MvPolynomial in
lemma pderiv_comm' (i a : ι) (p : MvPolynomial ι ℝ) :
    pderiv i (pderiv a p) = pderiv a (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    rcases eq_or_ne k a with rfl | hka <;> rcases eq_or_ne k i with rfl | hki <;>
      simp [pderiv_mul, pderiv_X_self, pderiv_X_of_ne, *] <;> ring

lemma sum_pi_succ {M : Type*} [AddCommMonoid M] (m : ℕ) (F : (Fin (m+1) → ι) → M) :
    ∑ w, F w = ∑ a : ι, ∑ w' : Fin m → ι, F (Fin.cons a w') := by
  rw [← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]; rfl

lemma ofFn_cons' {m : ℕ} (a : ι) (w : Fin m → ι) :
    List.ofFn (Fin.cons a w : Fin (m+1) → ι) = a :: List.ofFn w := by
  simp [List.ofFn_succ]

lemma wickRaise_add (a : ι) (p q : MvPolynomial ι ℝ) :
    wickRaise a (p + q) = wickRaise a p + wickRaise a q := by
  simp [wickRaise, mul_add]; ring

lemma wickRaise_sum {κ : Type*} (s : Finset κ) (a : ι) (f : κ → MvPolynomial ι ℝ) :
    wickRaise a (∑ k ∈ s, f k) = ∑ k ∈ s, wickRaise a (f k) := by
  simp [wickRaise, Finset.mul_sum, map_sum, Finset.sum_sub_distrib]

lemma wickRaise_C_mul (a : ι) (r : ℝ) (p : MvPolynomial ι ℝ) :
    wickRaise a (MvPolynomial.C r * p) = MvPolynomial.C r * wickRaise a p := by
  simp [wickRaise, MvPolynomial.pderiv_C_mul]; ring

lemma pderiv_wickRaise (i a : ι) (p : MvPolynomial ι ℝ) :
    MvPolynomial.pderiv i (wickRaise a p) =
      (if i = a then p else 0) + wickRaise a (MvPolynomial.pderiv i p) := by
  unfold wickRaise
  rw [map_sub, MvPolynomial.pderiv_mul, pderiv_comm' i a]
  rcases eq_or_ne a i with rfl | h
  · simp; ring
  · simp [MvPolynomial.pderiv_X_of_ne h, Ne.symm h]

lemma wickL_succ (m : ℕ) (H : List ι → ℝ) :
    wickL (m+1) H = ∑ a : ι, wickRaise a (wickL m (fun u => H (a :: u))) := by
  unfold wickL
  rw [sum_pi_succ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [wickRaise_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [ofFn_cons', wickRaise_C_mul]; rfl

lemma plainL_succ (m : ℕ) (H : List ι → ℝ) :
    plainL (m+1) H = ∑ a : ι, MvPolynomial.X a * plainL m (fun u => H (a :: u)) := by
  unfold plainL
  rw [sum_pi_succ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [ofFn_cons']; simp only [plainWord]; ring

lemma wickL_zero (H : List ι → ℝ) : wickL 0 H = MvPolynomial.C (H []) := by
  simp [wickL, wickWord]

lemma plainL_zero (H : List ι → ℝ) : plainL 0 H = MvPolynomial.C (H []) := by
  simp [plainL, plainWord]

lemma wickL_C_mul (m : ℕ) (r : ℝ) (H : List ι → ℝ) :
    MvPolynomial.C r * wickL m H = wickL m (fun u => r * H u) := by
  simp [wickL, Finset.mul_sum, mul_assoc]

lemma wickL_sum' {κ : Type*} [Fintype κ] (m : ℕ) (H : κ → List ι → ℝ) :
    ∑ k, wickL m (H k) = wickL m (fun u => ∑ k, H k u) := by
  simp only [wickL, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma wickL_congr (m : ℕ) (H K : List ι → ℝ) (h : ∀ u, H u = K u) :
    wickL m H = wickL m K := by
  rw [show H = K from funext h]

/-- Lemma D. -/
lemma pderiv_wickL (m : ℕ) : ∀ (H : List ι → ℝ), (∀ u v : List ι, u.Perm v → H u = H v) →
    ∀ i : ι, MvPolynomial.pderiv i (wickL (m+1) H) =
      MvPolynomial.C ((m:ℝ)+1) * wickL m (fun u => H (i :: u)) := by
  induction m with
  | zero =>
    intro H _ i
    rw [wickL_succ, map_sum]
    simp only [pderiv_wickRaise, wickL_zero, MvPolynomial.pderiv_C, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp [wickRaise]
  | succ m ih =>
    intro H hH i
    rw [wickL_succ, map_sum]
    simp only [pderiv_wickRaise, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    have hs : ∀ a : ι, ∀ u v : List ι, u.Perm v → H (a :: u) = H (a :: v) :=
      fun a u v h => hH _ _ (h.cons a)
    simp only [fun a => ih (fun u => H (a :: u)) (hs a) i]
    have : ∀ a : ι, wickL m (fun u => H (a :: i :: u)) = wickL m (fun u => H (i :: a :: u)) :=
      fun a => wickL_congr _ _ _ fun u => hH _ _ (List.Perm.swap _ _ _)
    simp only [this, wickRaise_C_mul]
    rw [← Finset.mul_sum, ← wickL_succ m (fun u => H (i :: u))]
    push_cast
    rw [show MvPolynomial.C ((m:ℝ)+1+1) = 1 + MvPolynomial.C ((m:ℝ)+1) by simp; ring]
    ring


lemma traceL_zero (G : List ι → ℝ) (u : List ι) : traceL 0 G u = G u := by
  simp [traceL, dblL]

lemma dblL_cons {l : ℕ} (i : ι) (c : Fin l → ι) :
    dblL (Fin.cons i c : Fin (l+1) → ι) = i :: i :: dblL c := by
  simp [dblL, ofFn_cons']

lemma traceL_symm (l : ℕ) (G : List ι → ℝ) (hG : ∀ u v : List ι, u.Perm v → G u = G v) :
    ∀ u v : List ι, u.Perm v → traceL l G u = traceL l G v := by
  intro u v h
  exact Finset.sum_congr rfl fun c _ => hG _ _ (h.append_left _)

lemma traceL_cons (l : ℕ) (G : List ι → ℝ) (hG : ∀ u v : List ι, u.Perm v → G u = G v)
    (i : ι) (u : List ι) :
    traceL l (fun v => G (i :: v)) u = traceL l G (i :: u) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  exact hG _ _ (List.perm_middle).symm

lemma traceL_succ (l : ℕ) (G : List ι → ℝ) (hG : ∀ u v : List ι, u.Perm v → G u = G v)
    (u : List ι) :
    ∑ i : ι, traceL l (fun v => G (i :: v)) (i :: u) = traceL (l+1) G u := by
  unfold traceL
  rw [sum_pi_succ]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
  rw [dblL_cons]
  exact hG _ _ ((List.perm_middle).cons i)

lemma X_mul_eq (i : ι) (p : MvPolynomial ι ℝ) :
    MvPolynomial.X i * p = wickRaise i p + MvPolynomial.pderiv i p := by
  simp [wickRaise]

lemma step_lemma (n l : ℕ) (G : List ι → ℝ) (hG : ∀ u v : List ι, u.Perm v → G u = G v) :
    ∑ i : ι, MvPolynomial.X i * wickL n (traceL l (fun v => G (i :: v))) =
      wickL (n+1) (traceL l G) +
        MvPolynomial.C (n:ℝ) * wickL (n-1) (traceL (l+1) G) := by
  simp only [X_mul_eq, Finset.sum_add_distrib]
  congr 1
  · rw [wickL_succ]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact wickL_congr _ _ _ fun u => traceL_cons l G hG i u
  · cases n with
    | zero => simp [wickL_zero]
    | succ n =>
      have hsym : ∀ i : ι, ∀ u v : List ι, u.Perm v →
          traceL l (fun w => G (i :: w)) u = traceL l (fun w => G (i :: w)) v :=
        fun i => traceL_symm l _ (fun u v h => hG _ _ (h.cons i))
      simp only [fun i => pderiv_wickL n _ (hsym i) i]
      rw [← Finset.mul_sum, wickL_sum']
      push_cast
      try simp only [Nat.add_sub_cancel]
      congr 1
      exact wickL_congr _ _ _ fun u => traceL_succ l G hG u

def cc : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | j+1, l+1 => cc j (l+1) + (j - 2*l) * cc j l

lemma cc_zero_of_lt : ∀ (j l : ℕ), j < 2 * l → cc j l = 0
  | 0, 0, h => by omega
  | 0, _+1, _ => rfl
  | _+1, 0, h => by omega
  | j+1, l+1, h => by
    simp only [cc]
    rw [cc_zero_of_lt j (l+1) (by omega)]
    rcases Nat.lt_or_ge j (2*l) with h' | h'
    · rw [cc_zero_of_lt j l h']; simp
    · rw [show j - 2*l = 0 by omega]; simp

lemma cc_j_zero : ∀ j, cc j 0 = 1
  | 0 => rfl
  | _+1 => rfl

lemma plain_cc (j : ℕ) : ∀ (G : List ι → ℝ), (∀ u v : List ι, u.Perm v → G u = G v) →
    plainL j G = ∑ l ∈ Finset.range (j + 1),
      MvPolynomial.C ((cc j l : ℝ)) * wickL (j - 2 * l) (traceL l G) := by
  induction j with
  | zero =>
    intro G _
    simp [plainL_zero, wickL_zero, traceL_zero, cc]
  | succ j ih =>
    intro G hG
    rw [plainL_succ]
    simp only [fun a => ih (fun u => G (a :: u)) (fun u v h => hG _ _ (h.cons a)),
      Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_left_comm (MvPolynomial.X _), ← Finset.mul_sum]
    simp only [step_lemma _ _ G hG]
    have hterm : ∀ l ∈ Finset.range (j+1),
        MvPolynomial.C ((cc j l : ℝ)) * (wickL (j - 2*l + 1) (traceL l G) +
          MvPolynomial.C ((j - 2*l : ℕ) : ℝ) * wickL (j - 2*l - 1) (traceL (l+1) G)) =
        MvPolynomial.C ((cc j l : ℝ)) * wickL (j + 1 - 2*l) (traceL l G) +
          MvPolynomial.C (((j - 2*l) * cc j l : ℕ) : ℝ) *
            wickL (j + 1 - 2*(l+1)) (traceL (l+1) G) := by
      intro l _
      rcases Nat.lt_or_ge j (2*l) with h | h
      · rw [cc_zero_of_lt j l h]; simp
      · rw [show j - 2*l + 1 = j + 1 - 2*l by omega,
          show j - 2*l - 1 = j + 1 - 2*(l+1) by omega]
        push_cast
        simp only [map_mul]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' _ (j+1)]
    simp only [cc, Nat.cast_add, map_add, add_mul, Finset.sum_add_distrib]
    have h1 : ∑ l ∈ Finset.range (j+1),
        MvPolynomial.C ((cc j l : ℝ)) * wickL (j + 1 - 2*l) (traceL l G) =
        ∑ l ∈ Finset.range (j+1),
          MvPolynomial.C ((cc j (l+1) : ℝ)) * wickL (j + 1 - 2*(l+1)) (traceL (l+1) G) +
        MvPolynomial.C ((cc j 0 : ℝ)) * wickL (j + 1 - 2*0) (traceL 0 G) := by
      rw [← Finset.sum_range_succ' (fun l =>
        MvPolynomial.C ((cc j l : ℝ)) * wickL (j + 1 - 2*l) (traceL l G)) (j+1),
        Finset.sum_range_succ _ (j+1), cc_zero_of_lt j (j+1) (by omega)]
      simp
    rw [h1, cc_j_zero]
    ring

lemma cQ_spec (l r : ℕ) :
    cQ (2*l + r) l = ((2*l+r).factorial : ℚ) / ((l.factorial : ℚ) * 2^l * (r.factorial : ℚ)) := by
  simp [cQ]

lemma cc_eq : ∀ (j l : ℕ), 2 * l ≤ j → (cc j l : ℚ) = cQ j l
  | 0, 0, _ => by simp [cc, cQ]
  | 0, _+1, h => by omega
  | j+1, 0, _ => by
    have := cQ_spec 0 (j+1)
    simp only [Nat.mul_zero, Nat.zero_add, Nat.factorial_zero, Nat.cast_one, pow_zero,
      one_mul] at this
    rw [this, div_self (by positivity)]; simp [cc]
  | j+1, l+1, h => by
    simp only [cc]
    obtain ⟨r, rfl⟩ : ∃ r, j = 2*l + 1 + r := ⟨j - (2*l+1), by omega⟩
    rw [show 2*l + 1 + r - 2*l = r + 1 by omega]
    have hl := cc_eq (2*l+1+r) l (by omega)
    rw [show 2*l+1+r = 2*l + (r+1) by omega] at hl
    rw [show 2*l+1+r+1 = 2*(l+1) + r by omega, cQ_spec]
    have hs' : ∀ s, r = s + 1 → (cc (2*l+1+r) (l+1) : ℚ) = cQ (2*l+1+r) (l+1) :=
      fun s hrs => cc_eq (2*l+1+r) (l+1) (by omega)
    rcases r with _ | s
    · rw [cc_zero_of_lt _ (l+1) (by omega)]
      push_cast
      rw [show 2*l+1+0 = 2*l+(0+1) by omega, hl, cQ_spec]
      have hA : (((2*(l+1)+0).factorial : ℕ) : ℚ) = (2*l+2) * ((2*l+(0+1)).factorial : ℚ) := by
        rw [show 2*(l+1)+0 = 2*l+(0+1)+1 by omega, Nat.factorial_succ]; push_cast; ring
      rw [hA]
      simp only [Nat.factorial_succ, Nat.factorial_zero]
      push_cast
      field_simp
      ring
    · have hs := hs' s rfl
      rw [show 2*l+1+(s+1) = 2*(l+1) + s by omega, cQ_spec] at hs
      push_cast
      rw [show 2*l+1+(s+1) = 2*(l+1) + s by omega, hs]
      rw [show 2*(l+1)+s = 2*l+(s+1+1) by omega, hl, cQ_spec]
      have hA : (((2*(l+1)+(s+1)).factorial : ℕ) : ℚ) =
          (2*l+s+3) * ((2*l+(s+1+1)).factorial : ℚ) := by
        rw [show 2*(l+1)+(s+1) = 2*l+(s+1+1)+1 by omega, Nat.factorial_succ]; push_cast; ring
      rw [hA]
      generalize ((2*l+(s+1+1)).factorial : ℚ) = A
      simp only [Nat.factorial_succ]
      push_cast
      field_simp
      ring
termination_by j _ _ => j
decreasing_by all_goals omega

theorem plain_expand (j : ℕ) (G : List ι → ℝ) (hG : ∀ u v : List ι, u.Perm v → G u = G v) :
    plainL j G = ∑ l ∈ Finset.range (j / 2 + 1),
      MvPolynomial.C ((cQ j l : ℚ) : ℝ) * wickL (j - 2 * l) (traceL l G) := by
  rw [plain_cc j G hG]
  symm
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : j / 2 + 1 ≤ j + 1))]
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [← cc_eq j l (by omega)]
    simp
  · intro l _ hl
    rw [Finset.mem_range] at hl
    rw [cc_zero_of_lt j l (by omega)]
    simp


end WickExp

open BstLean.Part36 (DD)

/-! The chaos kernels of `w_S` and the identification of order `s` with `q_S`. -/

def pm (α : CoefIdxD n d) : Mono n d := ⟨α.1, α.2.1⟩

noncomputable def Aker (k : ℕ) (T : Tens n) (s : ℕ) (S : Finset (Fin n)) (m : ℕ)
    (α : Fin m → CoefIdxD n d) : ℝ :=
  Real.sqrt (rhoD n (s * d)) * ∑ l ∈ (Finset.range (k + 1)).filter (fun l => m + 2 * l ≤ k),
    (∫ x, phiSq d x ^ l * (∏ t, phiM x (pm (α t))) * ∏ a ∈ S, x a ∂uniformSphere n) *
      aT n d T (m + 2 * l) l (fun t => (α ⟨t.1, by have := t.2; omega⟩).2.2)

/-! Step a/b: `uJ` as a plain polynomial. -/

lemma mapMD_eq (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) (a : Fin n) :
    BstLean.Part36.mapMD Z x a =
      ∑ β : CoefIdxD n d, if β.2.2 = a then Z β * phiM x (pm β) else 0 := by
  classical
  unfold BstLean.Part36.mapMD BstLean.Part36.coefD
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range (fun i => ∑ β : Sym (Fin n) i,
    (if h : i < d + 1 then Z ⟨⟨i, h⟩, (β, a)⟩ else 0) * BstLean.Part36.monoVal x β.1)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro β _
  rw [Finset.sum_ite_eq' Finset.univ a]
  simp [pm, phiM, i.2]


noncomputable def Tl (T : Tens n) (j : ℕ) (v : List (Fin n)) : ℝ :=
  if h : v.length = j then T j (fun t => v.get (Fin.cast h.symm t)) else 0

noncomputable def Gx (T : Tens n) (j : ℕ) (x : Fin n → ℝ) (u : List (CoefIdxD n d)) : ℝ :=
  Tl T j (u.map (fun α => α.2.2)) * (u.map (fun α => phiM x (pm α))).prod

lemma Tl_ofFn (T : Tens n) {j : ℕ} (w : Fin j → Fin n) : Tl T j (List.ofFn w) = T j w := by
  unfold Tl
  rw [dif_pos (List.length_ofFn)]
  congr 1
  funext t
  simp

lemma Gx_ofFn (T : Tens n) {j : ℕ} (x : Fin n → ℝ) (α : Fin j → CoefIdxD n d) :
    Gx T j x (List.ofFn α) = T j (fun t => (α t).2.2) * ∏ t, phiM x (pm (α t)) := by
  unfold Gx
  rw [List.map_ofFn, List.map_ofFn, Tl_ofFn, List.prod_ofFn]
  rfl

lemma eval_plainL {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (G : List ι → ℝ) (Z : ι → ℝ) :
    MvPolynomial.eval Z (plainL m G) = ∑ α : Fin m → ι, G (List.ofFn α) * ∏ t, Z (α t) := by
  simp [plainL, plainWord_ofFn]

lemma eval_wickL {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (G : List ι → ℝ) (Z : ι → ℝ) :
    MvPolynomial.eval Z (wickL m G) =
      ∑ α : Fin m → ι, G (List.ofFn α) * MvPolynomial.eval Z (wickWord (List.ofFn α)) := by
  simp [wickL]

lemma uJ_eq (T : Tens n) (j : ℕ) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    uJ T j Z x = MvPolynomial.eval Z (plainL j (Gx T j x)) := by
  classical
  rw [eval_plainL]
  unfold uJ contr
  simp_rw [mapMD_eq, Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_eq_single (fun t => (α t).2.2)]
  · rw [Gx_ofFn]
    simp only [if_true]
    rw [Finset.prod_mul_distrib]
    ring
  · intro w _ hw
    obtain ⟨t, ht⟩ : ∃ t, (α t).2.2 ≠ w t := by
      by_contra h
      push_neg at h
      exact hw (funext fun t => (h t).symm)
    rw [Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht]), mul_zero]
  · simp


private lemma orbit_perm {α : Type} [Fintype α] {s : ℕ} (u w : Fin s → α)
    (h : mset u = mset w) : ∃ σ : Equiv.Perm (Fin s), w ∘ σ = u := by
  classical
  have hcard (a : α) : Fintype.card {t : Fin s // u t = a} =
      Fintype.card {t : Fin s // w t = a} := by
    have hh := congrArg (Multiset.count a) h
    simpa only [mset, Multiset.count_map, Multiset.countP_eq_card_filter,
      ← Finset.filter_val, Fintype.card_subtype, Finset.card_def, eq_comm] using hh
  let e (a : α) := Fintype.equivOfCardEq (hcard a)
  let σ := (Equiv.sigmaFiberEquiv u).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv w))
  refine ⟨σ, ?_⟩
  funext t
  exact (e (u t) ⟨t, rfl⟩).property

lemma Tl_perm (T : Tens n) (j : ℕ) (hT : IsSymmT (T j)) (u v : List (Fin n)) (h : u.Perm v) :
    Tl T j u = Tl T j v := by
  unfold Tl
  by_cases hu : u.length = j
  · have hv : v.length = j := h.length_eq ▸ hu
    rw [dif_pos hu, dif_pos hv]
    have hm : mset (fun t : Fin j => u.get (Fin.cast hu.symm t)) =
        mset (fun t : Fin j => v.get (Fin.cast hv.symm t)) := by
      unfold mset
      rw [Fin.univ_val_map, Fin.univ_val_map]
      have e1 : List.ofFn (fun t : Fin j => u.get (Fin.cast hu.symm t)) = u := by
        apply List.ext_get <;> simp [hu]
      have e2 : List.ofFn (fun t : Fin j => v.get (Fin.cast hv.symm t)) = v := by
        apply List.ext_get <;> simp [hv]
      rw [e1, e2]
      exact Multiset.coe_eq_coe.mpr h
    obtain ⟨σ, hσ⟩ := orbit_perm _ _ hm
    rw [← hσ]
    exact hT σ _
  · have hv : ¬ v.length = j := h.length_eq ▸ hu
    rw [dif_neg hu, dif_neg hv]

lemma Gx_perm (T : Tens n) (j : ℕ) (hT : IsSymmT (T j)) (x : Fin n → ℝ)
    (u v : List (CoefIdxD n d)) (h : u.Perm v) : Gx T j x u = Gx T j x v := by
  unfold Gx
  rw [Tl_perm T j hT _ _ (h.map _), (h.map _).prod_eq]


lemma dblL_succ {X : Type*} {l : ℕ} (c : Fin (l + 1) → X) :
    dblL c = c 0 :: c 0 :: dblL (fun t => c t.succ) := by
  simp [dblL, List.ofFn_succ]

lemma dblL_length {X : Type*} {l : ℕ} (c : Fin l → X) : (dblL c).length = 2 * l := by
  induction l with
  | zero => simp [dblL]
  | succ l ih => rw [dblL_succ]; simp [ih]; ring

lemma dblL_getElem {X : Type*} {l : ℕ} (c : Fin l → X) (i : ℕ) (h : i < (dblL c).length) :
    (dblL c)[i] = c ⟨i / 2, by rw [dblL_length] at h; omega⟩ := by
  induction l generalizing i with
  | zero => simp [dblL] at h
  | succ l ih =>
    simp only [dblL_succ]
    rcases i with _ | _ | i
    · rfl
    · rfl
    · simp only [List.getElem_cons_succ]
      rw [ih]
      congr 1
      ext
      simp only [Fin.val_succ]
      omega

lemma dblL_map {X Y : Type*} {l : ℕ} (c : Fin l → X) (f : X → Y) :
    (dblL c).map f = dblL (fun t => f (c t)) := by
  induction l with
  | zero => simp [dblL]
  | succ l ih => rw [dblL_succ, dblL_succ]; simp [ih]

lemma dblL_prod {l : ℕ} (c : Fin l → ℝ) : (dblL c).prod = ∏ t, c t ^ 2 := by
  induction l with
  | zero => simp [dblL]
  | succ l ih => rw [dblL_succ]; simp [ih, Fin.prod_univ_succ]; ring

lemma Tl_glue (T : Tens n) (m l : ℕ) (c : Fin l → Fin n) (w : Fin m → Fin n) :
    Tl T (m + 2 * l) (dblL c ++ List.ofFn w) =
      T (m + 2 * l) (glue (m + 2 * l) l c (fun t => w ⟨t.1, by have := t.2; omega⟩)) := by
  unfold Tl
  have hlen : (dblL c ++ List.ofFn w).length = m + 2 * l := by
    simp [dblL_length]; ring
  rw [dif_pos hlen]
  congr 1
  funext t
  unfold glue
  simp only [List.get_eq_getElem, Fin.val_cast]
  split_ifs with ht
  · rw [List.getElem_append_left (by rw [dblL_length]; exact ht), dblL_getElem]
  · rw [List.getElem_append_right (by rw [dblL_length]; omega)]
    simp [dblL_length]

def eι : CoefIdxD n d ≃ Mono n d × Fin n where
  toFun α := (pm α, α.2.2)
  invFun q := ⟨q.1.1, (q.1.2, q.2)⟩
  left_inv α := rfl
  right_inv q := rfl

lemma sum_split {l : ℕ} (F : (Fin l → CoefIdxD n d) → ℝ) :
    ∑ c : Fin l → CoefIdxD n d, F c =
      ∑ p : Fin l → Mono n d, ∑ a : Fin l → Fin n, F (fun t => eι.symm (p t, a t)) := by
  let E : (Fin l → CoefIdxD n d) ≃ (Fin l → Mono n d) × (Fin l → Fin n) :=
    (Equiv.arrowCongr (Equiv.refl _) eι).trans (Equiv.arrowProdEquivProdArrow _ _ _)
  rw [← Fintype.sum_prod_type', ← E.symm.sum_comp]
  rfl

lemma traceL_Gx (T : Tens n) (m l : ℕ) (x : Fin n → ℝ) (α : Fin m → CoefIdxD n d) :
    traceL l (Gx T (m + 2 * l) x) (List.ofFn α) =
      phiSq d x ^ l * (∏ t, phiM x (pm (α t))) *
        trL l (T (m + 2 * l)) (fun t => (α ⟨t.1, by have := t.2; omega⟩).2.2) := by
  unfold traceL Gx trL
  rw [sum_split]
  simp only [List.map_append, dblL_map, List.map_ofFn, List.prod_append, dblL_prod,
    List.prod_ofFn, Tl_glue]
  simp only [Function.comp_def]
  change ∑ p : Fin l → Mono n d, ∑ a : Fin l → Fin n,
      T (m + 2 * l) (glue (m + 2 * l) l a _) * ((∏ t, phiM x (p t) ^ 2) * ∏ t, phiM x (pm (α t))) = _
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hp : (∑ p : Fin l → Mono n d, ∏ t, phiM x (p t) ^ 2) = phiSq d x ^ l := by
    rw [← Fintype.prod_sum (fun (_ : Fin l) (p : Mono n d) => phiM x p ^ 2)]
    simp [phiSq]
  rw [hp]
  ring


lemma integrand_cont {m : ℕ} (l : ℕ) (p : Fin m → Mono n d) (S : Finset (Fin n)) :
    Continuous (fun x : Fin n → ℝ => phiSq d x ^ l * (∏ t, phiM x (p t)) * ∏ a ∈ S, x a) := by
  apply Continuous.mul
  · apply (phiSq_cont.pow l).mul
    exact continuous_finsetProd _ (fun t _ => continuous_mono (p t).2.val)
  · exact continuous_finsetProd _ (fun a _ => continuous_apply a)

def mlSet (k m : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter (fun l => m + 2 * l ≤ k ∧ 1 ≤ m + 2 * l)

lemma reindex_jl (k : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 k, ∑ l ∈ Finset.range (j / 2 + 1), g j l =
      ∑ m ∈ Finset.range (k + 1), ∑ l ∈ mlSet k m, g (m + 2 * l) l := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_nbij' (fun p => ⟨p.1 - 2 * p.2, p.2⟩) (fun q => ⟨q.1 + 2 * q.2, q.2⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range, mlSet, Finset.mem_filter] at hp ⊢
    omega
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range, mlSet, Finset.mem_filter] at hq ⊢
    omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at hp
    ext <;> simp; omega
  · intro q hq
    ext <;> simp
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at hp
    simp only
    congr 1
    omega

lemma Pcal_expand (k : ℕ) (T : Tens n) (hT : TSymm k T) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    Pcal k T Z x = ∑ m ∈ Finset.range (k + 1), ∑ l ∈ mlSet k m, ∑ α : Fin m → CoefIdxD n d,
      aT n d T (m + 2 * l) l (fun t => (α ⟨t.1, by have := t.2; omega⟩).2.2) *
        (phiSq d x ^ l * ∏ t, phiM x (pm (α t))) *
          MvPolynomial.eval Z (wickWord (List.ofFn α)) := by
  unfold Pcal
  have h1 (j : ℕ) (hj : j ∈ Finset.Icc 1 k) : uJ T j Z x / Real.sqrt (DD n d) ^ j =
      ∑ l ∈ Finset.range (j / 2 + 1), (cQ j l : ℝ) / Real.sqrt (DD n d) ^ j *
        MvPolynomial.eval Z (wickL (j - 2 * l) (traceL l (Gx T j x))) := by
    have hj' := Finset.mem_Icc.mp hj
    rw [uJ_eq, plain_expand j _ (Gx_perm T j (hT j hj'.1 hj'.2) x)]
    simp only [map_sum, map_mul, MvPolynomial.eval_C, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [Finset.sum_congr rfl h1]
  rw [reindex_jl k (fun j l => (cQ j l : ℝ) / Real.sqrt (DD n d) ^ j *
        MvPolynomial.eval Z (wickL (j - 2 * l) (traceL l (Gx T j x))))]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro l _
  simp only [Nat.add_sub_cancel, eval_wickL, traceL_Gx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  unfold aT
  ring


noncomputable def Ims (l : ℕ) {m : ℕ} (p : Fin m → Mono n d) (S : Finset (Fin n)) : ℝ :=
  ∫ x, phiSq d x ^ l * (∏ t, phiM x (p t)) * ∏ a ∈ S, x a ∂uniformSphere n

lemma wS_expand (hn : 1 ≤ n) (k : ℕ) (T : Tens n) (hT : TSymm k T) (S : Finset (Fin n))
    (Z : CoefIdxD n d → ℝ) :
    wS k T S Z = ∑ m ∈ Finset.range (k + 1), ∑ l ∈ mlSet k m, ∑ α : Fin m → CoefIdxD n d,
      Real.sqrt (rhoD n S.card) *
        aT n d T (m + 2 * l) l (fun t => (α ⟨t.1, by have := t.2; omega⟩).2.2) *
          Ims l (fun t => pm (α t)) S * MvPolynomial.eval Z (wickWord (List.ofFn α)) := by
  unfold wS
  simp_rw [Pcal_expand k T hT Z, Finset.sum_mul]
  have hI {m : ℕ} (l : ℕ) (α : Fin m → CoefIdxD n d) (c e : ℝ) :
      Integrable (fun x : Fin n → ℝ => c * (phiSq d x ^ l * ∏ t, phiM x (pm (α t))) * e *
        ∏ a ∈ S, x a) (uniformSphere n) := by
    have h := (sphere_cont_integrable hn (integrand_cont (d := d) l (fun t => pm (α t)) S)).const_mul (c * e)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun l _ =>
    integrable_finsetSum _ (fun α _ => hI l α _ _)))]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun α _ => hI l α _ _)), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_finsetSum _ (fun α _ => hI l α _ _), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  have he : (fun x : Fin n → ℝ => aT n d T (m + 2 * l) l (fun t => (α ⟨t.1, by have := t.2; omega⟩).2.2) *
        (phiSq d x ^ l * ∏ t, phiM x (pm (α t))) *
          MvPolynomial.eval Z (wickWord (List.ofFn α)) * ∏ a ∈ S, x a) =
      fun x => (aT n d T (m + 2 * l) l (fun t => (α ⟨t.1, by have := t.2; omega⟩).2.2) *
          MvPolynomial.eval Z (wickWord (List.ofFn α))) *
        (phiSq d x ^ l * (∏ t, phiM x (pm (α t))) * ∏ a ∈ S, x a) := by
    funext x; ring
  rw [he, integral_const_mul]
  unfold Ims
  ring


lemma monoVal_sum {κ : Type*} (s : Finset κ) (q : κ → Multiset (Fin n)) (x : Fin n → ℝ) :
    BstLean.Part36.monoVal x (∑ t ∈ s, q t) = ∏ t ∈ s, BstLean.Part36.monoVal x (q t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [BstLean.Part36.monoVal]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ← ih]
    simp [BstLean.Part36.monoVal, Multiset.map_add, Multiset.prod_add]

lemma monoVal_add (x : Fin n → ℝ) (a b : Multiset (Fin n)) :
    BstLean.Part36.monoVal x (a + b) = BstLean.Part36.monoVal x a * BstLean.Part36.monoVal x b := by
  simp [BstLean.Part36.monoVal, Multiset.map_add, Multiset.prod_add]

/-- `phiSq^l · x^R` as a sum of monomials. -/
lemma phiSq_pow_mono (l : ℕ) (R : Multiset (Fin n)) (x : Fin n → ℝ) :
    phiSq d x ^ l * BstLean.Part36.monoVal x R =
      ∑ c : Fin l → Mono n d, BstLean.Part36.monoVal x
        ((∑ t, ((c t).2.val + (c t).2.val)) + R) := by
  have hp : phiSq d x ^ l = ∑ c : Fin l → Mono n d, ∏ t, phiM x (c t) ^ 2 := by
    rw [← Fintype.prod_sum (fun (_ : Fin l) (p : Mono n d) => phiM x p ^ 2)]
    simp [phiSq]
  rw [hp, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [monoVal_add, monoVal_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  rw [monoVal_add, pow_two]
  rfl

lemma sphere_mono (hn : 1 ≤ n) (e : Multiset (Fin n)) :
    Integrable (fun x => BstLean.Part36.monoVal x e) (uniformSphere n) ∧
    ∫ x, BstLean.Part36.monoVal x e ∂uniformSphere n =
      BstLean.Part36.gpm e / rhoD n (Multiset.card e / 2) :=
  BstLean.Part36.sphere_multiset (uniformSphere n)
    (BstLean.Part33.uniformSphere_prod n (Multiset.card e) hn) e le_rfl

lemma phiSq_mono_integral (hn : 1 ≤ n) (l : ℕ) (R : Multiset (Fin n)) :
    ∫ x, phiSq d x ^ l * BstLean.Part36.monoVal x R ∂uniformSphere n =
      ∑ c : Fin l → Mono n d,
        BstLean.Part36.gpm ((∑ t, ((c t).2.val + (c t).2.val)) + R) /
          rhoD n (Multiset.card ((∑ t, ((c t).2.val + (c t).2.val)) + R) / 2) := by
  simp_rw [phiSq_pow_mono]
  rw [integral_finsetSum _ (fun c _ => (sphere_mono hn _).1)]
  exact Finset.sum_congr rfl (fun c _ => (sphere_mono hn _).2)

lemma phiSq_mono_odd (hn : 1 ≤ n) (l : ℕ) (R : Multiset (Fin n)) (a : Fin n)
    (ha : Odd (R.count a)) :
    ∫ x, phiSq d x ^ l * BstLean.Part36.monoVal x R ∂uniformSphere n = 0 := by
  classical
  rw [phiSq_mono_integral hn]
  apply Finset.sum_eq_zero
  intro c _
  have hz : BstLean.Part36.gpm ((∑ t, ((c t).2.val + (c t).2.val)) + R) = 0 := by
    unfold BstLean.Part36.gpm
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    unfold BstLean.Part29.gaussMom
    rw [if_neg]
    rw [Multiset.count_add, Multiset.count_sum']
    simp only [Multiset.count_add]
    intro he
    have h2 : Even (∑ t, ((c t).2.val.count a + (c t).2.val.count a)) := by
      apply Finset.even_sum
      intro t _
      exact ⟨_, rfl⟩
    exact (Nat.not_even_iff_odd.mpr ha) ((Nat.even_add.mp he).mp h2)
  rw [hz, zero_div]


lemma exists_perm_map (S S' : Finset (Fin n)) (h : S.card = S'.card) :
    ∃ σ : Equiv.Perm (Fin n), S.map σ.toEmbedding = S' := by
  classical
  let e : {x // x ∈ S} ≃ {x // x ∈ S'} :=
    Fintype.equivOfCardEq (by simp [h])
  refine ⟨e.extendSubtype, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact e.extendSubtype_mem x hx
  · rw [Finset.card_map, h]

lemma gpm_map (σ : Equiv.Perm (Fin n)) (e : Multiset (Fin n)) :
    BstLean.Part36.gpm (e.map σ) = BstLean.Part36.gpm e := by
  classical
  unfold BstLean.Part36.gpm
  rw [← Equiv.prod_comp σ]
  apply Finset.prod_congr rfl
  intro a _
  rw [Multiset.count_map_eq_count' _ _ σ.injective]

lemma J_perm (hn : 1 ≤ n) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (l : ℕ) :
    ∫ x, phiSq d x ^ l * BstLean.Part36.monoVal x
        ((S.map σ.toEmbedding).val + (S.map σ.toEmbedding).val) ∂uniformSphere n =
      ∫ x, phiSq d x ^ l * BstLean.Part36.monoVal x (S.val + S.val) ∂uniformSphere n := by
  classical
  rw [phiSq_mono_integral hn, phiSq_mono_integral hn]
  let μ : Mono n d ≃ Mono n d := Equiv.sigmaCongrRight (fun i => Sym.equivCongr σ)
  rw [← (Equiv.arrowCongr (Equiv.refl (Fin l)) μ).sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  have he : (∑ t, (((Equiv.arrowCongr (Equiv.refl (Fin l)) μ) c t).2.val +
        ((Equiv.arrowCongr (Equiv.refl (Fin l)) μ) c t).2.val)) +
        ((S.map σ.toEmbedding).val + (S.map σ.toEmbedding).val) =
      ((∑ t, ((c t).2.val + (c t).2.val)) + (S.val + S.val)).map σ := by
    have hms : ∀ f : Fin l → Multiset (Fin n), Multiset.map σ (∑ t, f t) = ∑ t, Multiset.map σ (f t) :=
      fun f => map_sum (Multiset.mapAddMonoidHom (σ : Fin n → Fin n)) f Finset.univ
    rw [Multiset.map_add, hms]
    simp only [Finset.map_val, Multiset.map_add, Equiv.coe_toEmbedding]
    congr 1
  rw [he, gpm_map, Multiset.card_map]


def Qof {m : ℕ} (p : Fin m → Mono n d) : Multiset (Fin n) := ∑ t, (p t).2.val

lemma Qof_card {m : ℕ} (p : Fin m → Mono n d) : Multiset.card (Qof p) ≤ m * d := by
  unfold Qof
  have hc := map_sum Multiset.cardHom (fun t => (p t).2.val) Finset.univ
  change Multiset.cardHom (∑ t, (p t).2.val) ≤ _
  rw [hc]
  calc ∑ t, Multiset.cardHom (p t).2.val ≤ ∑ _t : Fin m, d := by
        apply Finset.sum_le_sum
        intro t _
        change Multiset.card (p t).2.val ≤ d
        rw [(p t).2.2]
        have := (p t).1.2
        omega
    _ = m * d := by simp

lemma Ims_eq_mono (l : ℕ) {m : ℕ} (p : Fin m → Mono n d) (S : Finset (Fin n)) :
    Ims l p S = ∫ x, phiSq d x ^ l * BstLean.Part36.monoVal x (Qof p + S.val) ∂uniformSphere n := by
  unfold Ims
  congr 1
  funext x
  rw [monoVal_add, Qof, monoVal_sum, mul_assoc]
  rfl

lemma Ims_low (hn : 1 ≤ n) (hd : 1 ≤ d) {s : ℕ} (S : Finset (Fin n)) (hS : S.card = s * d)
    {m : ℕ} (hm : m < s) (p : Fin m → Mono n d) (l : ℕ) : Ims l p S = 0 := by
  classical
  rw [Ims_eq_mono]
  obtain ⟨a, haS, haQ⟩ : ∃ a ∈ S, a ∉ Qof p := by
    by_contra h
    push_neg at h
    have h1 : S ⊆ (Qof p).toFinset := fun a ha => Multiset.mem_toFinset.mpr (h a ha)
    have h2 := Finset.card_le_card h1
    have h3 := Multiset.toFinset_card_le (Qof p)
    have h4 := Qof_card p
    have h5 : m * d < s * d := Nat.mul_lt_mul_of_pos_right hm (by omega)
    omega
  apply phiSq_mono_odd hn l _ a
  rw [Multiset.count_add, Multiset.count_eq_zero.mpr haQ, Multiset.count_eq_one_of_mem S.nodup haS]
  exact odd_one

lemma Ims_mid (hn : 1 ≤ n) (hd : 1 ≤ d) {s : ℕ} (S : Finset (Fin n)) (hS : S.card = s * d)
    (hsd : s * d ≤ n) (p : Fin s → Mono n d) (l : ℕ) :
    Ims l p S = if Qof p = S.val then nuC n d s l / rhoD n (s * d) else 0 := by
  classical
  rw [Ims_eq_mono]
  split_ifs with hQ
  · rw [hQ]
    let S0 : Finset (Fin n) := Finset.univ.filter (fun a => a.val < s * d)
    have hcard : S0.card = s * d := by
      let e : Fin (s * d) ↪ Fin n := ⟨Fin.castLE hsd, Fin.castLE_injective hsd⟩
      have he : S0 = Finset.univ.map e := by
        ext a
        simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
        constructor
        · intro ha
          exact ⟨⟨a.val, ha⟩, Fin.ext rfl⟩
        · rintro ⟨b, rfl⟩
          exact b.isLt
      rw [he, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    obtain ⟨σ, hσ⟩ := exists_perm_map S S0 (by rw [hS, hcard])
    have hJ := J_perm (d := d) hn σ S l
    rw [hσ] at hJ
    rw [← hJ]
    have hr : 0 < rhoD n (s * d) := by
      unfold rhoD
      apply Finset.prod_pos
      intro t _
      have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      positivity
    unfold nuC
    rw [mul_div_assoc, div_self hr.ne', mul_one]
    congr 1
    funext x
    congr 1
    rw [monoVal_add]
    unfold BstLean.Part36.monoVal
    rw [← Finset.prod_filter (fun a : Fin n => a.val < s * d) (fun a => x a ^ 2)]
    change _ = ∏ a ∈ S0, x a ^ 2
    rw [Finset.prod_pow, pow_two]
    rfl
  · obtain ⟨a, ha⟩ : ∃ a, Odd ((Qof p + S.val).count a) := by
      by_cases h : ∃ a ∈ S, a ∉ Qof p
      · obtain ⟨a, haS, haQ⟩ := h
        refine ⟨a, ?_⟩
        rw [Multiset.count_add, Multiset.count_eq_zero.mpr haQ,
          Multiset.count_eq_one_of_mem S.nodup haS]
        exact odd_one
      · exfalso
        push_neg at h
        have h1 : S ⊆ (Qof p).toFinset := fun a ha => Multiset.mem_toFinset.mpr (h a ha)
        have h2 := Finset.card_le_card h1
        have h3 := Multiset.toFinset_card_le (Qof p)
        have h4 := Qof_card p
        have hnd : (Qof p).Nodup := by
          apply Multiset.toFinset_card_eq_card_iff_nodup.mp
          omega
        have heq : S = (Qof p).toFinset :=
          Finset.eq_of_subset_of_card_le h1 (by omega)
        apply hQ
        rw [heq, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
    exact phiSq_mono_odd hn l _ a ha


lemma pderiv_wickWord_notMem {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    ∀ w : List ι, i ∉ w → MvPolynomial.pderiv i (wickWord w) = 0
  | [], _ => by simp [wickWord]
  | a :: w, h => by
    have hia : i ≠ a := fun e => h (e ▸ List.mem_cons_self)
    have hw : i ∉ w := fun e => h (List.mem_cons_of_mem a e)
    simp only [wickWord]
    rw [pderiv_wickRaise, if_neg hia, pderiv_wickWord_notMem i w hw]
    simp [wickRaise]

lemma wickWord_nodup {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ w : List ι, w.Nodup → wickWord w = plainWord w
  | [], _ => rfl
  | a :: w, h => by
    have h' := List.nodup_cons.mp h
    simp only [wickWord, plainWord, wickRaise]
    rw [pderiv_wickWord_notMem a w h'.1, wickWord_nodup w h'.2, sub_zero]

lemma nodup_sum_disjoint {m : ℕ} (f : Fin m → Multiset (Fin n)) (h : (∑ t, f t).Nodup)
    (t t' : Fin m) (htt : t ≠ t') : Disjoint (f t) (f t') := by
  classical
  have hs : ∑ u, f u = f t + (f t' + ∑ u ∈ (Finset.univ.erase t).erase t', f u) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨htt.symm, Finset.mem_univ t'⟩)]
  rw [hs] at h
  have h1 := (Multiset.nodup_add.mp h).2.2
  exact (Multiset.disjoint_add_right.mp h1).1

lemma nodup_sum_each {m : ℕ} (f : Fin m → Multiset (Fin n)) (h : (∑ t, f t).Nodup)
    (t : Fin m) : (f t).Nodup := by
  classical
  have hs : ∑ u, f u = f t + ∑ u ∈ Finset.univ.erase t, f u := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
  rw [hs] at h
  exact (Multiset.nodup_add.mp h).1

lemma part_card (hd : 1 ≤ d) {s : ℕ} (S : Finset (Fin n)) (hS : S.card = s * d)
    (p : Fin s → Mono n d) (hQ : Qof p = S.val) (t : Fin s) : (p t).1 = Fin.last d := by
  classical
  by_contra hne
  have hlt : ((p t).1 : ℕ) < d := by
    have := (p t).1.2
    have h2 : ((p t).1 : ℕ) ≠ d := fun e => hne (Fin.ext e)
    omega
  have hc := congrArg Multiset.card hQ
  have hsum := map_sum Multiset.cardHom (fun t => (p t).2.val) Finset.univ
  unfold Qof at hc
  change Multiset.cardHom (∑ t, (p t).2.val) = _ at hc
  rw [hsum] at hc
  simp only [Finset.card_val, hS] at hc
  have : ∑ u, Multiset.cardHom (p u).2.val < ∑ _u : Fin s, d := by
    apply Finset.sum_lt_sum
    · intro u _
      change Multiset.card (p u).2.val ≤ d
      rw [(p u).2.2]; have := (p u).1.2; omega
    · exact ⟨t, Finset.mem_univ t, by change Multiset.card (p t).2.val < d; rw [(p t).2.2]; exact hlt⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  rw [hc, mul_comm] at this
  exact lt_irrefl _ this


lemma recon (q : CoefIdxD n d) (h1 : q.1 = Fin.last d) (h2 : q.2.1.val.Nodup)
    (h : Multiset.card q.2.1.val.toFinset.val = d) :
    (⟨Fin.last d, (⟨q.2.1.val.toFinset.val, h⟩, q.2.2)⟩ : CoefIdxD n d) = q := by
  obtain ⟨i, β, a⟩ := q
  simp only at h1 h2 h ⊢
  subst h1
  congr
  rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr h2]

lemma parts_sum {s : ℕ} (S : Finset (Fin n)) (π : Fin s → Finset (Fin n)) (hπ : π ∈ parts d s S) :
    ∑ t, (π t).val = S.val := by
  classical
  unfold parts at hπ
  obtain ⟨_, hdis, hU⟩ := (Finset.mem_filter.mp hπ).2
  have hpd : ((Finset.univ : Finset (Fin s)) : Set (Fin s)).PairwiseDisjoint π :=
    fun t _ t' _ htt => hdis t t' htt
  have h1 : (Finset.univ.disjiUnion π hpd).val = ∑ t, (π t).val := rfl
  rw [← h1, Finset.disjiUnion_eq_biUnion, hU]

lemma Vs_eq (hd : 1 ≤ d) (k : ℕ) (T : Tens n) {s : ℕ} (hs : 1 ≤ s)
    (S : Finset (Fin n)) (hS : S.card = s * d) (hn : 1 ≤ n) (hsd : s * d ≤ n) (Z : CoefIdxD n d → ℝ) :
    ∑ l ∈ mlSet k s, ∑ α : Fin s → CoefIdxD n d,
      Real.sqrt (rhoD n S.card) *
        aT n d T (s + 2 * l) l (fun t => (α ⟨t.1, by have := t.2; omega⟩).2.2) *
          Ims l (fun t => pm (α t)) S * MvPolynomial.eval Z (wickWord (List.ofFn α)) =
      qS (bEff n d k T s) S Z := by
  classical
  have hr : 0 < rhoD n (s * d) := by
    unfold rhoD
    apply Finset.prod_pos
    intro t _
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hsq : Real.sqrt (rhoD n (s * d)) / rhoD n (s * d) = (Real.sqrt (rhoD n (s * d)))⁻¹ := by
    have h := Real.sq_sqrt hr.le
    have hp := Real.sqrt_pos.mpr hr
    field_simp
    rw [h]
  have hml : mlSet k s = (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k) := by
    unfold mlSet
    apply Finset.filter_congr
    intro l _
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, by omega⟩
  -- step 1: collapse to the filter of partitions
  have step1 : ∑ l ∈ mlSet k s, ∑ α : Fin s → CoefIdxD n d,
      Real.sqrt (rhoD n S.card) *
        aT n d T (s + 2 * l) l (fun t => (α ⟨t.1, by have := t.2; omega⟩).2.2) *
          Ims l (fun t => pm (α t)) S * MvPolynomial.eval Z (wickWord (List.ofFn α)) =
      ∑ α ∈ Finset.univ.filter (fun α : Fin s → CoefIdxD n d => Qof (fun t => pm (α t)) = S.val),
        (Real.sqrt (rhoD n (s * d)))⁻¹ * bEff n d k T s (fun t => (α t).2.2) *
          MvPolynomial.eval Z (wickWord (List.ofFn α)) := by
    rw [Finset.sum_comm, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro α _
    simp_rw [Ims_mid hn hd S hS hsd, hS]
    split_ifs with hQ
    · rw [← hsq, bEff, hml, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    · simp
  rw [step1]
  unfold qS contr
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  have hstruct : ∀ α : Fin s → CoefIdxD n d, Qof (fun t => pm (α t)) = S.val →
      (∀ t, (α t).1 = Fin.last d) ∧ (∀ t, (α t).2.1.val.Nodup) ∧
        (∀ t t', t ≠ t' → Disjoint (α t).2.1.val (α t').2.1.val) := by
    intro α hQ
    have hnd : (∑ t, (α t).2.1.val).Nodup := by
      have : Qof (fun t => pm (α t)) = ∑ t, (α t).2.1.val := rfl
      rw [← this, hQ]; exact S.nodup
    exact ⟨fun t => part_card hd S hS _ hQ t, nodup_sum_each _ hnd, nodup_sum_disjoint _ hnd⟩
  have hcardα : ∀ α : Fin s → CoefIdxD n d, Qof (fun t => pm (α t)) = S.val → ∀ t,
      Multiset.card (α t).2.1.val.toFinset.val = d := by
    intro α hQ t
    obtain ⟨h1, h2, _⟩ := hstruct α hQ
    change (α t).2.1.val.toFinset.card = d
    rw [Multiset.toFinset_card_of_nodup (h2 t), (α t).2.1.2, h1 t, Fin.val_last]
  have hcardx : ∀ x ∈ parts d s S ×ˢ (Finset.univ : Finset (Fin s → Fin n)), ∀ t,
      Multiset.card (x.1 t).val = d := by
    intro x hx t
    have := (Finset.mem_filter.mp (Finset.mem_product.mp hx).1).2.1 t
    exact this
  refine Finset.sum_bij'
    (fun α _ => ((fun t => (α t).2.1.val.toFinset), (fun t => (α t).2.2)))
    (fun x hx => fun t => (⟨Fin.last d, (⟨(x.1 t).val, hcardx x hx t⟩, x.2 t)⟩ : CoefIdxD n d))
    ?_ ?_ ?_ ?_ ?_
  · intro α hα
    have hQ := (Finset.mem_filter.mp hα).2
    obtain ⟨h1, h2, h3⟩ := hstruct α hQ
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
    unfold parts
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · intro t
      exact hcardα α hQ t
    · intro t t' htt
      exact Multiset.disjoint_toFinset.mpr (h3 t t' htt)
    · ext a
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Multiset.mem_toFinset]
      rw [← Finset.mem_val, ← hQ]
      unfold Qof
      rw [Multiset.mem_sum]
      simp [pm]
  · intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact parts_sum S x.1 (Finset.mem_product.mp hx).1
  · intro α hα
    have hQ := (Finset.mem_filter.mp hα).2
    obtain ⟨h1, h2, _⟩ := hstruct α hQ
    funext t
    exact recon (α t) (h1 t) (h2 t) (hcardα α hQ t)
  · intro x hx
    ext t
    · simp
    · rfl
  · intro α hα
    have hQ := (Finset.mem_filter.mp hα).2
    obtain ⟨h1, h2, h3⟩ := hstruct α hQ
    have hinj : Function.Injective α := by
      intro t t' he
      by_contra htt
      have hdj := h3 t t' htt
      rw [he] at hdj
      have hz : (α t').2.1.val = ⊥ := disjoint_self.mp hdj
      have hc := congrArg Multiset.card hz
      rw [(α t').2.1.2, h1 t'] at hc
      simp at hc
      omega
    rw [wickWord_nodup _ (List.nodup_ofFn.mpr hinj), plainWord_ofFn, MvPolynomial.eval_prod]
    simp only [MvPolynomial.eval_X]
    have hcol : ∀ t, colP Z (α t).2.1.val.toFinset (α t).2.2 = Z (α t) := by
      intro t
      unfold colP
      have hc : (α t).2.1.val.toFinset.card = d := hcardα α hQ t
      simp only [hc, dite_true]
      exact congrArg Z (recon (α t) (h1 t) (h2 t) (hcardα α hQ t))
    simp only [hcol]
    ring


lemma wick_expansion (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (hkd : k * d ≤ n) (T : Tens n)
    (hT : TSymm k T) (s : ℕ) (hs : s ∈ Finset.Icc 1 k)
    (S : Finset (Fin n)) (hS : S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d))
    (Z : CoefIdxD n d → ℝ) :
    wS k T S Z - qS (bEff n d k T s) S Z =
      MvPolynomial.eval Z (∑ m ∈ Finset.Icc (s + 1) k, wickTensor (Aker k T s S m)) := by
  classical
  have hs' := Finset.mem_Icc.mp hs
  have hSc : S.card = s * d := (Finset.mem_powersetCard.mp hS).2
  have hsd : s * d ≤ n := le_trans (Nat.mul_le_mul_right d hs'.2) hkd
  rw [wS_expand hn k T hT S Z]
  rw [← Finset.sum_range_add_sum_Ico _ (show s ≤ k + 1 by omega),
    Finset.sum_eq_sum_Ico_succ_bot (show s < k + 1 by omega), Finset.Ico_add_one_right_eq_Icc]
  have hlow : ∑ m ∈ Finset.range s, ∑ l ∈ mlSet k m, ∑ α : Fin m → CoefIdxD n d,
      Real.sqrt (rhoD n S.card) *
        aT n d T (m + 2 * l) l (fun t => (α ⟨t.1, by have := t.2; omega⟩).2.2) *
          Ims l (fun t => pm (α t)) S * MvPolynomial.eval Z (wickWord (List.ofFn α)) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    apply Finset.sum_eq_zero
    intro l _
    apply Finset.sum_eq_zero
    intro α _
    rw [Ims_low hn hd S hSc (Finset.mem_range.mp hm)]
    ring
  rw [hlow, Vs_eq hd k T hs'.1 S hSc hn hsd Z, zero_add, add_sub_cancel_left, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' := Finset.mem_Icc.mp hm
  have hml : mlSet k m = (Finset.range (k + 1)).filter (fun l => m + 2 * l ≤ k) := by
    unfold mlSet
    apply Finset.filter_congr
    intro l _
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, by omega⟩
  unfold wickTensor Aker
  rw [hml, Finset.sum_comm, map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [hSc, MvPolynomial.eval_mul, MvPolynomial.eval_C, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  unfold Ims
  ring


/-! The kernel bound. -/

/-- Local copy of `frob_trL_le` (Part41Tensor). -/
lemma hb_frob_trL_le {ι : Type*} [Fintype ι] {j : ℕ} (l : ℕ)
    (hl : 2 * l ≤ j) (A : (Fin j → ι) → ℝ) :
    frob (trL l A) ≤ (Fintype.card ι : ℝ) ^ l * frob A := by
  classical
  let G : (Fin l → ι) × (Fin (j - 2 * l) → ι) → (Fin j → ι) :=
    fun p => glue j l p.1 p.2
  have hinj : Function.Injective G := by
    intro p q h
    apply Prod.ext
    · funext t
      have h' := congrFun h ⟨2 * t.val, by omega⟩
      simpa [G, glue, show 2 * t.val < 2 * l by omega] using h'
    · funext t
      have h' := congrFun h ⟨2 * l + t.val, by omega⟩
      simpa [G, glue, show ¬2 * l + t.val < 2 * l by omega] using h'
  have hsum : (∑ w, ∑ c, A (glue j l c w) ^ 2) ≤ frob A := by
    rw [Finset.sum_comm]
    change (∑ c, ∑ w, A (G (c, w)) ^ 2) ≤ frob A
    rw [← Fintype.sum_prod_type (fun p => A (G p) ^ 2)]
    calc
      _ = ∑ v ∈ Finset.univ.image G, A v ^ 2 := by
        rw [Finset.sum_image (fun p _ q _ h => hinj h)]
      _ ≤ frob A := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  unfold frob trL
  calc
    _ ≤ ∑ w, (Fintype.card ι : ℝ) ^ l * ∑ c, A (glue j l c w) ^ 2 := by
      apply Finset.sum_le_sum
      intro w hw
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : Fin l → ι => (1 : ℝ)) (fun c => A (glue j l c w))
      simpa using h
    _ = (Fintype.card ι : ℝ) ^ l * ∑ w, ∑ c, A (glue j l c w) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

lemma hb_trL_zero {j : ℕ} (A : (Fin j → Fin n) → ℝ) : trL 0 A = A := by
  funext w
  simp only [trL, Finset.univ_unique, Finset.sum_singleton]
  congr 1

lemma hb_aSq_zero (T : Tens n) (j : ℕ) :
    aSq n d T j 0 = frob (T j) / DD n d ^ j := by
  simp [aSq, hb_trL_zero, cQ, Nat.factorial_ne_zero]
  ring

lemma hb_aT_frob (T : Tens n) (j l : ℕ) :
    frob (aT n d T j l) = aSq n d T j l := by
  classical
  have hp : (Real.sqrt (DD n d) ^ j) ^ 2 = DD n d ^ j := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, Real.sq_sqrt (by unfold DD; positivity)]
  unfold frob aT aSq
  simp only [mul_pow, div_pow, hp]
  rw [← Finset.mul_sum]
  rfl

lemma hb_aSq_trace_le (T : Tens n) (j l : ℕ) (hl : 2 * l ≤ j) :
    aSq n d T j l ≤ (cQ j l : ℝ) ^ 2 * (n : ℝ) ^ l * aSq n d T j 0 := by
  have h := hb_frob_trL_le l hl (T j)
  simp only [Fintype.card_fin] at h
  rw [hb_aSq_zero]
  unfold aSq
  have hD : 0 ≤ DD n d := by unfold DD; positivity
  have hh := mul_le_mul_of_nonneg_left h
    (by positivity : 0 ≤ (cQ j l : ℝ) ^ 2 / DD n d ^ j)
  convert hh using 1 <;> ring

lemma hb_le_maxJ (k : ℕ) (g : ℕ → ℝ) (j : ℕ) (hj : j ∈ Finset.Icc 1 k) :
    g j ≤ maxJ k g := by
  have hm : g j ∈ (List.range' 1 k).map g := by
    apply List.mem_map.mpr
    refine ⟨j, ?_, rfl⟩
    simpa using (show 1 ≤ j ∧ j < 1 + k from
      ⟨(Finset.mem_Icc.mp hj).1, by have := (Finset.mem_Icc.mp hj).2; omega⟩)
  unfold maxJ
  generalize ((List.range' 1 k).map g) = xs at *
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    rcases List.mem_cons.mp hm with h | h
    · simpa [h] using le_max_left x (xs.foldr max 0)
    · exact (ih h).trans (le_max_right _ _)

lemma hb_frob_cast (s l : ℕ) (A : (Fin (s + 2 * l - 2 * l) → Fin n) → ℝ) :
    frob (fun w : Fin s → Fin n => A (fun t => w ⟨t.val, by have := t.isLt; omega⟩)) = frob A := by
  classical
  let e : (Fin s → Fin n) ≃ (Fin (s + 2 * l - 2 * l) → Fin n) :=
    Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl _)
  exact e.sum_comp (fun w => A w ^ 2)

lemma hb_tj_nonneg (k : ℕ) (T : Tens n) (j : ℕ) : 0 ≤ tj n d k T j := by
  unfold tj aSq frob
  have hD : 0 ≤ DD n d := by unfold DD; positivity
  positivity

def hbEqv (m : ℕ) : (Fin m → CoefIdxD n d) ≃ (Fin m → Mono n d) × (Fin m → Fin n) where
  toFun α := (fun t => pm (α t), fun t => (α t).2.2)
  invFun q := fun t => ⟨(q.1 t).1, ((q.1 t).2, q.2 t)⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma hb_sum_factor (m : ℕ) (F : (Fin m → Mono n d) → ℝ) (G : (Fin m → Fin n) → ℝ) :
    ∑ α : Fin m → CoefIdxD n d, F (fun t => pm (α t)) * G (fun t => (α t).2.2) =
      (∑ p, F p) * ∑ w, G w := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (hbEqv m) _ _ (fun _ => rfl)

noncomputable def Eint (S : Finset (Fin n)) (l : ℕ) {m : ℕ} (p : Fin m → Mono n d) : ℝ :=
  ∫ x, phiSq d x ^ l * (∏ t, phiM x (p t)) * ∏ a ∈ S, x a ∂uniformSphere n

lemma hb_frob_Aker (k : ℕ) (T : Tens n) (s : ℕ) (S : Finset (Fin n)) (m : ℕ) :
    frob (Aker (d := d) k T s S m) ≤
      ((Finset.range (k + 1)).filter (fun l => m + 2 * l ≤ k)).card *
      ∑ l ∈ (Finset.range (k + 1)).filter (fun l => m + 2 * l ≤ k),
        (∑ p : Fin m → Mono n d, Eint (d := d) S l p ^ 2 * rhoD n (s * d)) *
          aSq n d T (m + 2 * l) l := by
  set Lf := (Finset.range (k + 1)).filter (fun l => m + 2 * l ≤ k)
  have hρ : 0 ≤ rhoD n (s * d) := by unfold BstLean.Part36.rhoD; positivity
  set u : (Fin m → CoefIdxD n d) → ℕ → ℝ := fun α l =>
    Eint (d := d) S l (fun t => pm (α t)) *
      aT n d T (m + 2 * l) l (fun t => (α ⟨t.1, by have := t.2; omega⟩).2.2) with hu
  have hA : ∀ α, Aker (d := d) k T s S m α = Real.sqrt (rhoD n (s * d)) * ∑ l ∈ Lf, u α l :=
    fun _ => rfl
  unfold frob
  simp_rw [hA]
  calc ∑ α, (Real.sqrt (rhoD n (s * d)) * ∑ l ∈ Lf, u α l) ^ 2
      = ∑ α, rhoD n (s * d) * (∑ l ∈ Lf, u α l) ^ 2 := by
        congr 1; funext α; rw [mul_pow, Real.sq_sqrt hρ]
    _ ≤ ∑ α, rhoD n (s * d) * ((Lf.card : ℝ) * ∑ l ∈ Lf, u α l ^ 2) := by
        gcongr with α
        exact sq_sum_le_card_mul_sum_sq
    _ = (Lf.card : ℝ) * ∑ l ∈ Lf, rhoD n (s * d) * ∑ α, u α l ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun α _ => by ring
    _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun l hl => ?_
        have h1 : ∑ α, u α l ^ 2 = (∑ p : Fin m → Mono n d, Eint (d := d) S l p ^ 2) *
            ∑ w : Fin m → Fin n, aT n d T (m + 2 * l) l (fun t => w ⟨t.1, by have := t.2; omega⟩) ^ 2 := by
          rw [← hb_sum_factor]
          refine Finset.sum_congr rfl fun α _ => ?_
          simp only [hu, mul_pow]
        have h2 := hb_frob_cast (n := n) m l (aT n d T (m + 2 * l) l)
        unfold frob at h2
        rw [h1, h2, ← hb_aT_frob, ← Finset.sum_mul]; unfold frob
        ring

lemma hb_aSq_nonneg (T : Tens n) (j l : ℕ) : 0 ≤ aSq n d T j l := by
  rw [← hb_aT_frob]; unfold frob; positivity

lemma hb_card_L (k m : ℕ) (hm : m ≤ k) :
    ((Finset.range (k + 1)).filter (fun l => m + 2 * l ≤ k)).card = Ls k m + 1 := by
  have : (Finset.range (k + 1)).filter (fun l => m + 2 * l ≤ k) = Finset.range (Ls k m + 1) := by
    ext l; simp only [Finset.mem_filter, Finset.mem_range, Ls]; omega
  rw [this, Finset.card_range]

lemma hb_step_sm (k : ℕ) (T : Tens n) (s m : ℕ) (hm : m ≤ k)
    (hW : ∀ r m l : ℕ, (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      ∑ p : Fin m → Mono n d,
        (∫ x, phiSq d x ^ l * (∏ t, phiM x (p t)) * ∏ a ∈ S, x a ∂uniformSphere n) ^ 2 *
          rhoD n r) ≤ ((d : ℝ) + 1) ^ (m + 2 * l)) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d),
        (m.factorial : ℝ) * frob (Aker (d := d) k T s S m) ≤
      ∑ l ∈ (Finset.range (k + 1)).filter (fun l => m + 2 * l ≤ k),
        ((Ls k m : ℝ) + 1) * (m.factorial : ℝ) * (((d : ℝ) + 1) ^ (m + 2 * l) *
          ((cQ (m + 2 * l) l : ℝ) ^ 2 * (n : ℝ) ^ l * aSq n d T (m + 2 * l) 0)) := by
  set Lf := (Finset.range (k + 1)).filter (fun l => m + 2 * l ≤ k)
  set PS := (Finset.univ : Finset (Fin n)).powersetCard (s * d)
  have hc : (Lf.card : ℝ) = (Ls k m : ℝ) + 1 := by rw [hb_card_L k m hm]; push_cast; ring
  calc ∑ S ∈ PS, (m.factorial : ℝ) * frob (Aker (d := d) k T s S m)
      ≤ ∑ S ∈ PS, (m.factorial : ℝ) * ((Lf.card : ℝ) * ∑ l ∈ Lf,
          (∑ p : Fin m → Mono n d, Eint (d := d) S l p ^ 2 * rhoD n (s * d)) *
            aSq n d T (m + 2 * l) l) := by
        gcongr with S
        exact hb_frob_Aker k T s S m
    _ = ∑ l ∈ Lf, ((Ls k m : ℝ) + 1) * (m.factorial : ℝ) * (aSq n d T (m + 2 * l) l *
          ∑ S ∈ PS, ∑ p : Fin m → Mono n d, Eint (d := d) S l p ^ 2 * rhoD n (s * d)) := by
        rw [hc]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun S _ => ?_
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc aSq n d T (m + 2 * l) l *
              ∑ S ∈ PS, ∑ p : Fin m → Mono n d, Eint (d := d) S l p ^ 2 * rhoD n (s * d)
            ≤ ((cQ (m + 2 * l) l : ℝ) ^ 2 * (n : ℝ) ^ l * aSq n d T (m + 2 * l) 0) *
                ((d : ℝ) + 1) ^ (m + 2 * l) := by
              apply mul_le_mul (hb_aSq_trace_le T _ l (by omega)) (hW (s * d) m l)
              · exact Finset.sum_nonneg fun S _ => Finset.sum_nonneg fun p _ => by
                  have : 0 ≤ rhoD n (s * d) := by unfold BstLean.Part36.rhoD; positivity
                  positivity
              · have := hb_aSq_nonneg (d := d) T (m + 2 * l) 0
                positivity
          _ = _ := by ring

lemma hb_reindex (k : ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    ∑ s ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc (s + 1) k,
        ∑ l ∈ (Finset.range (k + 1)).filter (fun l => m + 2 * l ≤ k), F s m l =
      ∑ j ∈ Finset.Icc 1 k, ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l + 2 ≤ j),
        ∑ s ∈ Finset.Ico 1 (j - 2 * l), F s (j - 2 * l) l := by
  rw [Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨⟨x.1.2 + 2 * x.2, x.2⟩, x.1.1⟩)
    (fun y => ⟨⟨y.2, y.1.1 - 2 * y.1.2⟩, y.1.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨s, m⟩, l⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc,
      Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at h ⊢
    omega
  · rintro ⟨⟨j, l⟩, s⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc,
      Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at h ⊢
    omega
  · rintro ⟨⟨s, m⟩, l⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc,
      Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at h
    simp only [Nat.add_sub_cancel]
  · rintro ⟨⟨j, l⟩, s⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc,
      Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at h
    have : j - 2 * l + 2 * l = j := by omega
    simp only [this]
  · rintro ⟨⟨s, m⟩, l⟩ h
    simp only [Nat.add_sub_cancel]

theorem Aker_bound (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (T : Tens n)
    (hW : ∀ r m l : ℕ, (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      ∑ p : Fin m → Mono n d,
        (∫ x, phiSq d x ^ l * (∏ t, phiM x (p t)) * ∏ a ∈ S, x a ∂uniformSphere n) ^ 2 *
          rhoD n r) ≤ ((d : ℝ) + 1) ^ (m + 2 * l)) :
    ∑ s ∈ Finset.Icc 1 k,
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d),
          ∑ m ∈ Finset.Icc (s + 1) k, (m.factorial : ℝ) * frob (Aker (d := d) k T s S m)) /
            (n : ℝ) ^ (k - s) ≤ XiC n d k / n * ∑ j ∈ Finset.Icc 1 k, tj n d k T j := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set num : ℕ → ℕ → ℝ := fun m l => ((Ls k m : ℝ) + 1) * (m.factorial : ℝ) *
    (((d : ℝ) + 1) ^ (m + 2 * l) * ((cQ (m + 2 * l) l : ℝ) ^ 2 * (n : ℝ) ^ l *
      aSq n d T (m + 2 * l) 0)) with hnum
  set G : ℕ → ℝ := fun j => ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l + 2 ≤ j),
    ((Ls k (j - 2 * l) : ℝ) + 1) * ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ) ^ 2 *
      ((d : ℝ) + 1) ^ (2 * l) * PsiB n d (j - 2 * l) / ((n : ℝ) ^ l * (j.factorial : ℝ) * j) with hG
  have hGX : ∀ j ∈ Finset.Icc 1 k, G j ≤ XiC n d k := fun j hj => hb_le_maxJ k G j hj
  have stepA : ∑ s ∈ Finset.Icc 1 k,
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d),
          ∑ m ∈ Finset.Icc (s + 1) k, (m.factorial : ℝ) * frob (Aker (d := d) k T s S m)) /
            (n : ℝ) ^ (k - s) ≤
      ∑ s ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc (s + 1) k,
        ∑ l ∈ (Finset.range (k + 1)).filter (fun l => m + 2 * l ≤ k), num m l / (n : ℝ) ^ (k - s) := by
    refine Finset.sum_le_sum fun s hs => ?_
    simp only [← Finset.sum_div]
    gcongr
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun m hm => ?_
    exact hb_step_sm k T s m (Finset.mem_Icc.mp hm).2 hW
  have stepC : ∀ j ∈ Finset.Icc 1 k, G j / n * tj n d k T j =
      ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l + 2 ≤ j),
        ∑ s ∈ Finset.Ico 1 (j - 2 * l), num (j - 2 * l) l / (n : ℝ) ^ (k - s) := by
    intro j hj
    simp only [hG, PsiB, Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun s hs => ?_
    have hj' := Finset.mem_Icc.mp hj
    simp only [Finset.mem_filter, Finset.mem_range] at hl
    have hs' := Finset.mem_Ico.mp hs
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 * l := ⟨j - 2 * l, by omega⟩
    simp only [Nat.add_sub_cancel, hnum, tj]
    have he : k - s = (m - 1 - s) + l + 1 + (k - (m + 2 * l)) + l := by omega
    rw [he]
    have hj0 : ((m + 2 * l : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show m + 2 * l ≠ 0 by omega)
    have hfac : ((m + 2 * l).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    simp only [pow_add, pow_one]
    field_simp
  calc _ ≤ _ := stepA
    _ = _ := hb_reindex k (fun s m l => num m l / (n : ℝ) ^ (k - s))
    _ = ∑ j ∈ Finset.Icc 1 k, G j / n * tj n d k T j :=
        (Finset.sum_congr rfl fun j hj => (stepC j hj).symm)
    _ ≤ _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j hj => ?_
        gcongr
        · exact hb_tj_nonneg k T j
        · exact hGX j hj



/-- **Lemma `LF` (iii)** (crude constant): `E H_α ≤ (Ξ/n) Σ_j t_j`, and `H_α` is integrable. -/
theorem contam (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hkd : k * d ≤ n) (T : Tens n)
    (hT : TSymm k T) :
    Integrable (Halpha k T) (stdGauss (CoefIdxD n d)) ∧
    ∫ Z, Halpha k T Z ∂stdGauss (CoefIdxD n d) ≤ XiC n d k / n * ∑ j ∈ Finset.Icc 1 k, tj n d k T j := by
  refine ⟨Halpha_integrable hn k T, ?_⟩
  calc
    _ ≤ _ := contamination_of_wick_expansion hn k T (fun s S m => Aker (d := d) k T s S m)
        (fun s hs S hS Z => wick_expansion hn hd k hkd T hT s hs S hS Z)
    _ ≤ _ := Aker_bound hn hd k hk T (fun r m l => weighted_monomial_bessel hn r m l)


end BstLean.Part41
