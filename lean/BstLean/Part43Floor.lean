import BstLean.Part43Defs
import BstLean.Part41Contam

/-!
# Part 43, wave 1: the Gaussian mean floor and the pointwise cascade (Lemmas F, F′)

Paper: `proofs/option-m/43-arbitrary-degree-every-diagonal-bingham.tex`. Specification:
`delegations/answers/p43-spec-opus.md`. Replace each `sorry` by a proof. Do not edit the statements.
Do not use `native_decide` or `axiom` anywhere.

Suggested route.
* `phiSq_bounds`: `phiSq d x = Σ_{e ≤ d} h_e(u)`, `u = x∘x`; `h_0 = h_1(u) = 1` and `0 ≤ h_e(u) ≤ (Σu)^e = 1`.
* `floorF43` (Lemma F): the chaos-`m` coefficient of `𝒫(Z)(x)` is `X_m(x) = b_m(q(x)) ⊗ φ(x)^{⊗m}`
  (Hermite expansion of `T_j[y^{⊗j}]`, `y = Zφ ∼ N(0, q I)`, `c_{j,l} = cQ j l`). By Fubini and chaos
  orthogonality `E_Z Var_μ 𝒫 = Σ_m m! E_μ‖X_m − E_μ X_m‖²` (plus the `m = 0` term `≥ 0`). Keep the
  entries with exactly one linear slot `x_a` and constant slots elsewhere: each has `μ`-mean `0`
  (sign symmetry), and their squares sum to `m ‖b_m(q(x))‖² Σ_a x_a² = m ‖b_m(q(x))‖²`.
* `cascade43` (Lemma F′): copy `Part41Floor1.cascade` with `ν_{s,l} = q^l` (so `ν_{s,0} = 1` and
  `0 ≤ ν_{s,l} ≤ (d+1)^l`) and `bEff` replaced by `bq`.
-/

namespace BstLean.Part43

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD rhoD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT mset wordOf Tens TSymm fval varU sdU
  levels cQ kapQ muQ aT Nn uJ Pcal r2 rhoZ cS Bfix Pn epsS baseline thetaT rhoBar Kc GamP etaR etaK Lk
  orbSize heavyCount bQ In41)
open BstLean.Part40 (SphLaw SignSym)
open BstLean.Part41 (glue aSq tj maxJ Ls)

variable {n d : ℕ}

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


private lemma phiSq_ge_two (hd : 1 ≤ d) (x : Fin n → ℝ)
    (hx : ∑ a, x a ^ 2 = 1) : 2 ≤ phiSq d x := by
  classical
  let L : ℕ → ℝ := fun i => ∑ b : Sym (Fin n) i, BstLean.Part36.monoVal x b.val ^ 2
  have h0 : L 0 = 1 := by
    have hm (b : Sym (Fin n) 0) : BstLean.Part36.monoVal x b.val = 1 := by
      have hb : b.val = 0 := Multiset.card_eq_zero.mp b.property
      change (b.val.map x).prod = 1
      rw [hb]
      simp
    change (∑ b : Sym (Fin n) 0, BstLean.Part36.monoVal x b.val ^ 2) = 1
    rw [Finset.univ_unique, Finset.sum_singleton, hm]
    norm_num
  have h1 : L 1 = 1 := by
    have he := (Sym.oneEquiv : Fin n ≃ Sym (Fin n) 1).sum_comp
      (fun b => BstLean.Part36.monoVal x b.val ^ 2)
    calc
      L 1 = ∑ i : Fin n, BstLean.Part36.monoVal x (Sym.oneEquiv i).val ^ 2 := he.symm
      _ = ∑ i : Fin n, x i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        change (({i} : Multiset (Fin n)).map x).prod ^ 2 = x i ^ 2
        simp
      _ = 1 := hx
  let a : Fin (d + 1) := ⟨0, by omega⟩
  let b : Fin (d + 1) := ⟨1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
  have hL (i : ℕ) : 0 ≤ L i := Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold phiSq phiM
  rw [Fintype.sum_sigma]
  change 2 ≤ ∑ i : Fin (d + 1), L i.val
  calc
    2 = L a.val + L b.val := by norm_num [a, b, h0, h1]
    _ = ∑ i ∈ ({a, b} : Finset (Fin (d + 1))), L i.val := by simp [hab]
    _ ≤ ∑ i : Fin (d + 1), L i.val :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hL i.val)

theorem phiSq_bounds (hd : 1 ≤ d) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    2 ≤ phiSq d x ∧ phiSq d x ≤ (d : ℝ) + 1 := by
  exact ⟨phiSq_ge_two hd x hx, phiSq_le x hx⟩

private lemma sphere_cont_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  letI := hμ.prob
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hμ.sphere] with x hx
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

private lemma joint_integral_polynomial {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (p : JointPoly n d) :
    ∃ q : MvPolynomial (CoefIdxD n d) ℝ, ∀ Z,
      (∫ x, jointEval p Z x ∂μ) = MvPolynomial.eval Z q := by
  classical
  refine ⟨∑ e ∈ p.support, MvPolynomial.monomial e
    (∫ x, p.coeff e x ∂μ), ?_⟩
  intro Z
  have hE (x) : jointEval p Z x =
      ∑ e ∈ p.support, p.coeff e x * e.prod (fun i a => Z i ^ a) := by
    conv_lhs => unfold jointEval; rw [p.as_sum]
    simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
      Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply]
  simp_rw [hE]
  rw [integral_finsetSum _ (fun e _ =>
    (sphere_cont_integrable hμ (p.coeff e).continuous).mul_const _)]
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

private lemma jointEval_cont (p : JointPoly n d) (Z : CoefIdxD n d → ℝ) :
    Continuous (jointEval p Z) := by
  classical
  have he (x) : jointEval p Z x =
      ∑ e ∈ p.support, p.coeff e x * e.prod (fun i a => Z i ^ a) := by
    conv_lhs => unfold jointEval; rw [p.as_sum]
    simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
      Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply]
  simp_rw [show jointEval p Z = (fun x =>
    ∑ e ∈ p.support, p.coeff e x * e.prod (fun i a => Z i ^ a)) from funext he]
  exact continuous_finsetSum _ (fun e _ => (p.coeff e).continuous.mul_const _)

private lemma Pcal_variance_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (T : Tens n) :
    Integrable (fun Z : CoefIdxD n d → ℝ => varU μ (Pcal k T Z))
      (stdGauss (CoefIdxD n d)) := by
  classical
  letI := hμ.prob
  obtain ⟨p, hp⟩ := joint_integral_polynomial hμ (pJoint (d := d) k T)
  obtain ⟨q, hq⟩ := joint_integral_polynomial hμ (pJoint (d := d) k T ^ 2)
  have hc (Z : CoefIdxD n d → ℝ) : Continuous (Pcal k T Z) := by
    simpa only [show Pcal k T Z = jointEval (pJoint k T) Z from
      funext (fun x => (pJoint_eval k T Z x).symm)] using jointEval_cont (pJoint k T) Z
  have he (Z : CoefIdxD n d → ℝ) :
      varU μ (Pcal k T Z) = MvPolynomial.eval Z (q - p ^ 2) := by
    have hm := hp Z
    simp_rw [pJoint_eval] at hm
    have hs := hq Z
    have hh (x) : jointEval (pJoint (d := d) k T ^ 2) Z x = Pcal k T Z x ^ 2 := by
      simp only [jointEval, map_pow]
      rw [← jointEval, pJoint_eval]
    simp_rw [hh] at hs
    unfold varU
    have hi := sphere_cont_integrable hμ (hc Z)
    have hi2 := sphere_cont_integrable hμ ((hc Z).pow 2)
    have hip : Integrable (fun x => 2 * Pcal k T Z x * ∫ y, Pcal k T Z y ∂μ) μ :=
      (hi.const_mul 2).mul_const _
    have his : Integrable (fun x => Pcal k T Z x ^ 2 -
        2 * Pcal k T Z x * ∫ y, Pcal k T Z y ∂μ) μ := hi2.sub hip
    simp_rw [sub_sq]
    rw [integral_add (f := fun x => Pcal k T Z x ^ 2 -
        2 * Pcal k T Z x * ∫ y, Pcal k T Z y ∂μ)
      (g := fun _ => (∫ y, Pcal k T Z y ∂μ) ^ 2) his (integrable_const _),
      integral_sub (f := fun x => Pcal k T Z x ^ 2)
        (g := fun x => 2 * Pcal k T Z x * ∫ y, Pcal k T Z y ∂μ) hi2 hip]
    simp only [integral_const_mul, integral_mul_const, integral_const,
      probReal_univ, one_smul, hs, hm, map_sub, map_pow]
    ring
  rw [show (fun Z : CoefIdxD n d → ℝ => varU μ (Pcal k T Z)) =
    (fun Z => MvPolynomial.eval Z (q - p ^ 2)) from funext he]
  exact gaussian_eval_integrable (q - p ^ 2)

private lemma bq_feature_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (T : Tens n) (s : ℕ) :
    Integrable (fun x => frob (bq n d k T s (phiSq d x))) μ := by
  classical
  apply sphere_cont_integrable hμ
  unfold frob bq phiSq phiM
  apply continuous_finsetSum
  intro w hw
  apply Continuous.pow
  apply continuous_finsetSum
  intro l hl
  apply Continuous.mul_const
  apply Continuous.pow
  exact continuous_finsetSum _ (fun p _ => (continuous_mono p.2.val).pow 2)


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

private lemma wordDeriv_C_mul {ι : Type*} [DecidableEq ι]
    (w : List ι) (c : ℝ) (p : MvPolynomial ι ℝ) :
    wordDeriv w (MvPolynomial.C c * p) = MvPolynomial.C c * wordDeriv w p := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih => simp only [wordDeriv, MvPolynomial.pderiv_C_mul, ih]

private lemma gaussianExpectation_C {ι : Type*} [Fintype ι] (c : ℝ) :
    gaussianExpectation (MvPolynomial.C c : MvPolynomial ι ℝ) = c := by
  simp [gaussianExpectation]

private lemma gaussianExpectation_C_mul {ι : Type*} [Fintype ι]
    (c : ℝ) (p : MvPolynomial ι ℝ) :
    gaussianExpectation (MvPolynomial.C c * p) = c * gaussianExpectation p := by
  simpa only [MvPolynomial.smul_eq_C_mul, smul_eq_mul] using
    (gaussianExpectation (ι := ι)).map_smul c p


private lemma wordDeriv_wickL {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : List ι) (H : List ι → ℝ)
    (hH : ∀ u v, List.Perm u v → H u = H v) :
    wordDeriv w (BstLean.Part41.wickL w.length H) =
      MvPolynomial.C ((w.length.factorial : ℝ) * H w) := by
  induction w generalizing H with
  | nil => simp [wordDeriv, BstLean.Part41.wickL_zero]
  | cons i w ih =>
    simp only [wordDeriv, List.length_cons]
    rw [BstLean.Part41.pderiv_wickL _ H hH i, wordDeriv_C_mul,
      ih (fun u => H (i :: u)) (fun u v h => hH _ _ (h.cons i))]
    simp only [← map_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    congr 1
    ring

private lemma wickL_unfold {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (H : List ι → ℝ) : BstLean.Part41.wickL m H =
      ∑ w : Fin m → ι, MvPolynomial.C (H (List.ofFn w)) * wickWord (List.ofFn w) := by
  classical
  induction m generalizing H with
  | zero => simp [BstLean.Part41.wickL_zero, wickWord]
  | succ m ih =>
    rw [BstLean.Part41.wickL_succ, BstLean.Part41.sum_pi_succ]
    apply Finset.sum_congr rfl
    intro a ha
    change wickRaise a (BstLean.Part41.wickL m (fun u => H (a :: u))) = _
    rw [ih]
    simp only [BstLean.Part41.ofFn_cons', wickWord]
    unfold wickRaise
    simp only [Finset.mul_sum, map_sum, MvPolynomial.pderiv_C_mul,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    ring

private lemma wickL_cross {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (H K : List ι → ℝ)
    (hK : ∀ u v, List.Perm u v → K u = K v) :
    gaussianExpectation (BstLean.Part41.wickL m H * BstLean.Part41.wickL m K) =
      (m.factorial : ℝ) * ∑ w : Fin m → ι, H (List.ofFn w) * K (List.ofFn w) := by
  classical
  have he := wickL_unfold m H
  rw [he, Finset.sum_mul, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [mul_assoc, gaussianExpectation_C_mul, wickWord_adjoint]
  have hd := wordDeriv_wickL (List.ofFn w) K hK
  simp only [List.length_ofFn] at hd
  rw [hd, gaussianExpectation_C]
  ring

private lemma wickL_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m r : ℕ) (H K : List ι → ℝ) (hmr : m ≠ r) :
    gaussianExpectation (BstLean.Part41.wickL m H * BstLean.Part41.wickL r K) = 0 := by
  classical
  have he := wickL_unfold (ι := ι)
  rw [he m H, he r K]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro v hv
  apply Finset.sum_eq_zero
  intro w hw
  have hp : (MvPolynomial.C (H (List.ofFn w)) * wickWord (List.ofFn w)) *
      (MvPolynomial.C (K (List.ofFn v)) * wickWord (List.ofFn v)) =
      MvPolynomial.C (H (List.ofFn w) * K (List.ofFn v)) *
        (wickWord (List.ofFn w) * wickWord (List.ofFn v)) := by rw [map_mul]; ring
  rw [hp, gaussianExpectation_C_mul, wickWord_orthogonal _ _
    (by simpa only [List.length_ofFn] using hmr), mul_zero]

private lemma wickL_sum_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ℕ) (H : ℕ → List ι → ℝ)
    (hH : ∀ m ∈ S, ∀ u v, List.Perm u v → H m u = H m v) :
    gaussianExpectation ((∑ m ∈ S, BstLean.Part41.wickL m (H m)) ^ 2) =
      ∑ m ∈ S, (m.factorial : ℝ) * ∑ w : Fin m → ι, H m (List.ofFn w) ^ 2 := by
  classical
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_eq_single m]
  · simpa only [pow_two, Finset.mul_sum] using wickL_cross m (H m) (H m) (hH m hm)
  · intro r hr hrm
    exact wickL_orthogonal r m (H r) (H m) hrm
  · intro hnm
    exact (hnm hm).elim

private noncomputable def floorKernel (k : ℕ) (T : Tens n) (m : ℕ)
    (x : Fin n → ℝ) (u : List (CoefIdxD n d)) : ℝ :=
  ∑ l ∈ BstLean.Part41.mlSet k m,
    (cQ (m + 2 * l) l : ℝ) / Real.sqrt (DD n d) ^ (m + 2 * l) *
      BstLean.Part41.traceL l (BstLean.Part41.Gx T (m + 2 * l) x) u

private lemma floorKernel_symm (k : ℕ) (T : Tens n) (hT : TSymm k T) (m : ℕ)
    (x : Fin n → ℝ) (u v : List (CoefIdxD n d)) (huv : u.Perm v) :
    floorKernel k T m x u = floorKernel k T m x v := by
  classical
  unfold floorKernel
  apply Finset.sum_congr rfl
  intro l hl
  have hj := (Finset.mem_filter.mp hl).2
  rw [BstLean.Part41.traceL_symm l _
    (BstLean.Part41.Gx_perm T _ (hT _ hj.2 hj.1) x) u v huv]

private lemma floorKernel_ofFn (k : ℕ) (T : Tens n) (m : ℕ) (x : Fin n → ℝ)
    (α : Fin m → CoefIdxD n d) :
    floorKernel k T m x (List.ofFn α) =
      ∑ l ∈ BstLean.Part41.mlSet k m,
        aT n d T (m + 2 * l) l (fun t => (α ⟨t.val, by have := t.isLt; omega⟩).2.2) *
          (phiSq d x ^ l * ∏ t, phiM x (BstLean.Part41.pm (α t))) := by
  classical
  unfold floorKernel
  apply Finset.sum_congr rfl
  intro l hl
  rw [BstLean.Part41.traceL_Gx]
  unfold aT
  ring

private lemma floorKernel_cont (k : ℕ) (T : Tens n) (m : ℕ)
    (α : Fin m → CoefIdxD n d) : Continuous (fun x => floorKernel k T m x (List.ofFn α)) := by
  classical
  simp_rw [floorKernel_ofFn]
  apply continuous_finsetSum
  intro l hl
  apply Continuous.const_mul
  apply Continuous.mul
  · apply Continuous.pow
    unfold phiSq phiM
    exact continuous_finsetSum _ (fun p _ => (continuous_mono p.2.val).pow 2)
  · exact continuous_finsetProd _ (fun t _ => continuous_mono (α t).2.1.val)

private lemma Pcal_floorKernel (k : ℕ) (T : Tens n) (hT : TSymm k T)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    Pcal k T Z x = MvPolynomial.eval Z
      (∑ m ∈ Finset.range (k + 1), BstLean.Part41.wickL m (floorKernel k T m x)) := by
  classical
  unfold Pcal
  have h1 (j : ℕ) (hj : j ∈ Finset.Icc 1 k) :
      uJ T j Z x / Real.sqrt (DD n d) ^ j =
        ∑ l ∈ Finset.range (j / 2 + 1), (cQ j l : ℝ) / Real.sqrt (DD n d) ^ j *
          MvPolynomial.eval Z (BstLean.Part41.wickL (j - 2 * l)
            (BstLean.Part41.traceL l (BstLean.Part41.Gx T j x))) := by
    have hj' := Finset.mem_Icc.mp hj
    rw [BstLean.Part41.uJ_eq, BstLean.Part41.plain_expand j _
      (BstLean.Part41.Gx_perm T j (hT j hj'.1 hj'.2) x)]
    simp only [map_sum, map_mul, MvPolynomial.eval_C, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [Finset.sum_congr rfl h1, BstLean.Part41.reindex_jl]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Nat.add_sub_cancel, wickL_unfold, map_sum, map_mul,
    MvPolynomial.eval_C, floorKernel, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro l hl
  ring

private lemma floorKernel_bq (k : ℕ) (T : Tens n) (m : ℕ) (hm : 1 ≤ m)
    (x : Fin n → ℝ) (α : Fin m → CoefIdxD n d) :
    floorKernel k T m x (List.ofFn α) =
      bq n d k T m (phiSq d x) (fun t => (α t).2.2) *
        ∏ t, phiM x (BstLean.Part41.pm (α t)) := by
  classical
  rw [floorKernel_ofFn]
  have hs : BstLean.Part41.mlSet k m =
      (Finset.range (k + 1)).filter (fun l => m + 2 * l ≤ k) := by
    ext l
    simp only [BstLean.Part41.mlSet, Finset.mem_filter, Finset.mem_range]
    omega
  rw [hs]
  unfold bq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  ring

private noncomputable def centeredKernel (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n)
    (m : ℕ) (x : Fin n → ℝ) (u : List (CoefIdxD n d)) : ℝ :=
  floorKernel k T m x u - ∫ y, floorKernel k T m y u ∂μ

private lemma centeredKernel_cont (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n)
    (m : ℕ) (α : Fin m → CoefIdxD n d) :
    Continuous (fun x => centeredKernel μ k T m x (List.ofFn α)) :=
  (floorKernel_cont k T m α).sub continuous_const

private lemma centeredKernel_symm (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n)
    (hT : TSymm k T) (m : ℕ) (x : Fin n → ℝ)
    (u v : List (CoefIdxD n d)) (huv : u.Perm v) :
    centeredKernel μ k T m x u = centeredKernel μ k T m x v := by
  unfold centeredKernel
  simp_rw [floorKernel_symm k T hT m _ u v huv]

private lemma Pcal_centeredKernel {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (T : Tens n) (hT : TSymm k T) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    Pcal k T Z x - ∫ y, Pcal k T Z y ∂μ = MvPolynomial.eval Z
      (∑ m ∈ Finset.range (k + 1), BstLean.Part41.wickL m (centeredKernel μ k T m x)) := by
  classical
  simp_rw [Pcal_floorKernel k T hT, map_sum, wickL_unfold, map_sum,
    map_mul, MvPolynomial.eval_C]
  rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun α _ =>
    (sphere_cont_integrable hμ (floorKernel_cont k T m α)).mul_const _))]
  simp_rw [integral_finsetSum _ (fun α _ =>
    (sphere_cont_integrable hμ (floorKernel_cont k T _ α)).mul_const _), integral_mul_const]
  simp only [centeredKernel, sub_mul, Finset.sum_sub_distrib]

private lemma separated_integral {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {ι κ : Type*} [Fintype κ] (S : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (hF : ∀ i ∈ S, Continuous (F i)) :
    (∫ Z, ∫ x, ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) ∂μ ∂stdGauss κ) =
      ∫ x, ∫ Z, ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) ∂stdGauss κ ∂μ := by
  classical
  have hx (Z : κ → ℝ) :
      (∫ x, ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) ∂μ) =
        ∑ i ∈ S, (∫ x, F i x ∂μ) * MvPolynomial.eval Z (G i) := by
    rw [integral_finsetSum _ (fun i hi => (sphere_cont_integrable hμ (hF i hi)).mul_const _)]
    simp only [integral_mul_const]
  have hZ (x : Fin n → ℝ) :
      (∫ Z, ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) ∂stdGauss κ) =
        ∑ i ∈ S, F i x * ∫ Z, MvPolynomial.eval Z (G i) ∂stdGauss κ := by
    rw [integral_finsetSum _ (fun i _ => (gaussian_eval_integrable (G i)).const_mul _)]
    simp only [integral_const_mul]
  simp_rw [hx, hZ]
  rw [integral_finsetSum _ (fun i _ => (gaussian_eval_integrable (G i)).const_mul _),
    integral_finsetSum _ (fun i hi => (sphere_cont_integrable hμ (hF i hi)).mul_const _)]
  simp only [integral_const_mul, integral_mul_const]

private lemma separated_square_integral {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {ι κ : Type*} [Fintype κ] (S : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (hF : ∀ i ∈ S, Continuous (F i)) :
    (∫ Z, ∫ x, (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) ^ 2 ∂μ ∂stdGauss κ) =
      ∫ x, ∫ Z, (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) ^ 2 ∂stdGauss κ ∂μ := by
  classical
  have he (x : Fin n → ℝ) (Z : κ → ℝ) :
      (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) ^ 2 =
        ∑ ij ∈ S ×ˢ S, (F ij.1 x * F ij.2 x) * MvPolynomial.eval Z (G ij.1 * G ij.2) := by
    rw [pow_two, Finset.sum_mul, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul]
    ring
  simp_rw [he]
  apply separated_integral hμ
  intro ij hij
  exact (hF ij.1 (Finset.mem_product.mp hij).1).mul
    (hF ij.2 (Finset.mem_product.mp hij).2)

private lemma floor_energy_identity {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (T : Tens n) (hT : TSymm k T) :
    (∫ Z, varU μ (Pcal k T Z) ∂stdGauss (CoefIdxD n d)) =
      ∫ x, ∑ m ∈ Finset.range (k + 1), (m.factorial : ℝ) *
        ∑ α : Fin m → CoefIdxD n d, centeredKernel μ k T m x (List.ofFn α) ^ 2 ∂μ := by
  classical
  let S : Finset (Σ m : ℕ, Fin m → CoefIdxD n d) :=
    (Finset.range (k + 1)).sigma (fun _ => Finset.univ)
  let F (i : Σ m : ℕ, Fin m → CoefIdxD n d) (x : Fin n → ℝ) :=
    centeredKernel μ k T i.1 x (List.ofFn i.2)
  let G (i : Σ m : ℕ, Fin m → CoefIdxD n d) := wickWord (List.ofFn i.2)
  have hex (x : Fin n → ℝ) (Z : CoefIdxD n d → ℝ) :
      MvPolynomial.eval Z (∑ m ∈ Finset.range (k + 1),
        BstLean.Part41.wickL m (centeredKernel μ k T m x)) =
        ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) := by
    simp only [map_sum, wickL_unfold, map_sum, map_mul, MvPolynomial.eval_C,
      S, F, G, Finset.sum_sigma]
  unfold varU
  simp_rw [Pcal_centeredKernel hμ k T hT, hex]
  rw [separated_square_integral hμ S F G (fun i _ => centeredKernel_cont μ k T i.1 i.2)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp_rw [← hex]
  have he := wickL_sum_sq (ι := CoefIdxD n d) (Finset.range (k + 1)) (centeredKernel μ k T · x)
    (fun m _ => centeredKernel_symm μ k T hT m x)
  simpa only [gaussianExpectation, LinearMap.coe_mk, AddHom.coe_mk, map_pow] using he

private lemma mono_powers (x : Fin n → ℝ) (u : Multiset (Fin n)) :
    BstLean.Part36.monoVal x u = ∏ a, x a ^ u.count a := by
  classical
  induction u using Multiset.induction_on with
  | empty => simp [BstLean.Part36.monoVal]
  | @cons a u ih =>
    simp only [BstLean.Part36.monoVal, Multiset.map_cons, Multiset.prod_cons] at *
    rw [ih]
    simp only [Multiset.count_cons]
    have he (b : Fin n) : x b ^ (u.count b + (if b = a then 1 else 0)) =
        (if b = a then x a else 1) * x b ^ u.count b := by
      split_ifs with h
      · subst b; rw [pow_add, pow_one]; ring
      · simp
    simp_rw [he, Finset.prod_mul_distrib]
    simp

private lemma phiSq_flip (i : Fin n) (x : Fin n → ℝ) :
    phiSq d (BstLean.Part40.flipAt i x) = phiSq d x := by
  classical
  unfold phiSq
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [phiM, mono_powers, ← Finset.prod_pow, ← pow_mul,
    mul_comm _ 2, pow_mul]
  congr 1
  ext a
  by_cases h : a = i <;> simp [BstLean.Part40.flipAt, h]

private lemma odd_integral {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ)
    (i : Fin n) {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    (ho : ∀ x, f (BstLean.Part40.flipAt i x) = -f x) : (∫ x, f x ∂μ) = 0 := by
  have hm : Measurable (BstLean.Part40.flipAt i) := by
    apply Measurable.of_eval
    intro j
    dsimp [BstLean.Part40.flipAt]
    split_ifs <;> fun_prop
  have hi : (∫ x, f (BstLean.Part40.flipAt i x) ∂μ) = ∫ x, f x ∂μ := by
    rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable, hμ.flip i]
  simp_rw [ho] at hi
  rw [integral_neg] at hi
  linarith


private lemma bq_coord_cont (k : ℕ) (T : Tens n) (m : ℕ) (w : Fin m → Fin n) :
    Continuous (fun x : Fin n → ℝ => bq n d k T m (phiSq d x) w) := by
  classical
  unfold bq
  apply continuous_finsetSum
  intro l hl
  apply Continuous.mul_const
  apply Continuous.pow
  unfold phiSq phiM
  exact continuous_finsetSum _ (fun p _ => (continuous_mono p.2.val).pow 2)

private lemma bq_coord_odd_mean {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ)
    (k : ℕ) (T : Tens n) (m : ℕ) (w : Fin m → Fin n) (a : Fin n) :
    (∫ x, bq n d k T m (phiSq d x) w * x a ∂μ) = 0 := by
  apply odd_integral hμ a ((bq_coord_cont k T m w).mul (continuous_apply a))
  intro x
  change bq n d k T m (phiSq d (BstLean.Part40.flipAt a x)) w *
    BstLean.Part40.flipAt a x a = -(bq n d k T m (phiSq d x) w * x a)
  rw [phiSq_flip]
  simp [BstLean.Part40.flipAt]

private def floorConst : Mono n d := ⟨0, Sym.nil⟩

private def floorLinear (hd : 1 ≤ d) (a : Fin n) : Mono n d :=
  ⟨⟨1, by omega⟩, Sym.oneEquiv a⟩

private lemma phiM_floorConst (x : Fin n → ℝ) : phiM x (floorConst (d := d)) = 1 := by
  simp [phiM, floorConst, BstLean.Part36.monoVal]

private lemma phiM_floorLinear (hd : 1 ≤ d) (a : Fin n) (x : Fin n → ℝ) :
    phiM x (floorLinear hd a) = x a := by
  change (({a} : Multiset (Fin n)).map x).prod = x a
  simp

private def floorWord (hd : 1 ≤ d) {m : ℕ} (v : Fin m × Fin n × (Fin m → Fin n)) :
    Fin m → CoefIdxD n d := fun u =>
  let p : Mono n d := if u = v.1 then floorLinear hd v.2.1 else floorConst
  ⟨p.1, (p.2, v.2.2 u)⟩

private lemma floorWord_output (hd : 1 ≤ d) {m : ℕ}
    (v : Fin m × Fin n × (Fin m → Fin n)) :
    (fun u => (floorWord hd v u).2.2) = v.2.2 := rfl

private lemma floorWord_product (hd : 1 ≤ d) {m : ℕ}
    (v : Fin m × Fin n × (Fin m → Fin n)) (x : Fin n → ℝ) :
    (∏ u, phiM x (BstLean.Part41.pm (floorWord hd v u))) = x v.2.1 := by
  classical
  have he (u : Fin m) :
      phiM x (BstLean.Part41.pm (floorWord hd v u)) = if u = v.1 then x v.2.1 else 1 := by
    unfold floorWord
    split_ifs <;> simp [BstLean.Part41.pm,
      phiM_floorLinear, phiM_floorConst]
  simp_rw [he]
  simp

private lemma floorWord_injective (hd : 1 ≤ d) (m : ℕ) :
    Function.Injective (floorWord hd : (Fin m × Fin n × (Fin m → Fin n)) →
      (Fin m → CoefIdxD n d)) := by
  classical
  intro v v' h
  have ht : v.1 = v'.1 := by
    by_contra hne
    have hh := congrArg (fun α => (α v.1).1.val) h
    simp [floorWord, floorLinear, floorConst, hne] at hh
  have hw : v.2.2 = v'.2.2 := by
    funext u
    exact congrArg (fun α => (α u).2.2) h
  have ha : v.2.1 = v'.2.1 := by
    have hh := congrArg (fun α => BstLean.Part41.pm (α v.1)) h
    have hl : floorLinear hd v.2.1 = floorLinear hd v'.2.1 := by
      change (if v.1 = v.1 then floorLinear hd v.2.1 else floorConst) =
        (if v.1 = v'.1 then floorLinear hd v'.2.1 else floorConst) at hh
      rw [if_pos rfl, if_pos ht] at hh
      exact hh
    have hm := congrArg (fun p : Mono n d => p.2.val) hl
    change ({v.2.1} : Multiset (Fin n)) = {v'.2.1} at hm
    simpa using hm
  exact Prod.ext ht (Prod.ext ha hw)

private lemma centeredKernel_floorWord {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ)
    (hd : 1 ≤ d) (k : ℕ) (T : Tens n) (m : ℕ) (hm : 1 ≤ m)
    (v : Fin m × Fin n × (Fin m → Fin n)) (x : Fin n → ℝ) :
    centeredKernel μ k T m x (List.ofFn (floorWord hd v)) =
      bq n d k T m (phiSq d x) v.2.2 * x v.2.1 := by
  unfold centeredKernel
  simp_rw [floorKernel_bq k T m hm, floorWord_output, floorWord_product,
    bq_coord_odd_mean hμ k T m v.2.2 v.2.1]
  simp

private lemma floor_level_energy {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ)
    (hd : 1 ≤ d) (k : ℕ) (T : Tens n) (m : ℕ) (hm : 1 ≤ m)
    (x : Fin n → ℝ) (hx : ∑ a, x a ^ 2 = 1) :
    (m : ℝ) * frob (bq n d k T m (phiSq d x)) ≤
      ∑ α : Fin m → CoefIdxD n d, centeredKernel μ k T m x (List.ofFn α) ^ 2 := by
  classical
  let F : (Fin m → CoefIdxD n d) → ℝ :=
    fun α => centeredKernel μ k T m x (List.ofFn α) ^ 2
  have hsub : (∑ v : Fin m × Fin n × (Fin m → Fin n), F (floorWord hd v)) ≤
      ∑ α : Fin m → CoefIdxD n d, F α := by
    rw [← Finset.sum_image (fun v _ v' _ hh => floorWord_injective hd m hh)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
  have he : (∑ v : Fin m × Fin n × (Fin m → Fin n), F (floorWord hd v)) =
      (m : ℝ) * frob (bq n d k T m (phiSq d x)) := by
    simp only [F, centeredKernel_floorWord hμ hd k T m hm, mul_pow]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    have ha : (∑ a : Fin n, ∑ w : Fin m → Fin n,
        bq n d k T m (phiSq d x) w ^ 2 * x a ^ 2) =
        frob (bq n d k T m (phiSq d x)) := by
      simp only [← Finset.sum_mul]
      rw [← Finset.mul_sum, hx, mul_one]
      rfl
    simp only [ha, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [he] at hsub
  exact hsub

/-- **Lemma F** (Gaussian mean floor) for every sign-symmetric law on the sphere. -/
theorem floorF43 (hn : 1 ≤ n) (hd : 1 ≤ d) {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ) (k : ℕ)
    (T : Tens n) (hT : TSymm k T) :
    Integrable (fun Z => varU μ (Pcal k T Z)) (stdGauss (CoefIdxD n d)) ∧
    (∀ s, Integrable (fun x => frob (bq n d k T s (phiSq d x))) μ) ∧
    ∑ s ∈ Finset.Icc 1 k, (s.factorial : ℝ) * s * ∫ x, frob (bq n d k T s (phiSq d x)) ∂μ ≤
      ∫ Z, varU μ (Pcal k T Z) ∂stdGauss (CoefIdxD n d) := by
  refine ⟨Pcal_variance_integrable hμ.sph k T, bq_feature_integrable hμ.sph k T, ?_⟩
  classical
  let E (m : ℕ) (x : Fin n → ℝ) : ℝ := (m.factorial : ℝ) *
    ∑ α : Fin m → CoefIdxD n d, centeredKernel μ k T m x (List.ofFn α) ^ 2
  have hE (m : ℕ) : Integrable (E m) μ := by
    apply sphere_cont_integrable hμ.sph
    apply Continuous.const_mul
    exact continuous_finsetSum _ (fun α _ => (centeredKernel_cont μ k T m α).pow 2)
  have hB (m : ℕ) : Integrable (fun x => (m.factorial : ℝ) * m *
      frob (bq n d k T m (phiSq d x))) μ :=
    (bq_feature_integrable hμ.sph k T m).const_mul _
  have hmean : (∑ m ∈ Finset.Icc 1 k, (m.factorial : ℝ) * m *
      ∫ x, frob (bq n d k T m (phiSq d x)) ∂μ) =
      ∫ x, ∑ m ∈ Finset.Icc 1 k, (m.factorial : ℝ) * m *
        frob (bq n d k T m (phiSq d x)) ∂μ := by
    rw [integral_finsetSum _ (fun m _ => hB m)]
    simp only [integral_const_mul]
  rw [hmean, floor_energy_identity hμ.sph k T hT]
  apply integral_mono_ae (integrable_finsetSum _ (fun m _ => hB m))
    (integrable_finsetSum _ (fun m _ => hE m))
  filter_upwards [hμ.sph.sphere] with x hx
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 k, E m x := by
      apply Finset.sum_le_sum
      intro m hm
      have hh := mul_le_mul_of_nonneg_left
        (floor_level_energy hμ hd k T m (Finset.mem_Icc.mp hm).1 x hx)
        (Nat.cast_nonneg m.factorial : (0 : ℝ) ≤ m.factorial)
      simpa only [E, mul_assoc] using hh
    _ ≤ ∑ m ∈ Finset.range (k + 1), E m x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        have := Finset.mem_Icc.mp hm
        simp only [Finset.mem_range]
        omega
      · intro m hm hnm
        exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

private lemma trace_frob_le_local {ι : Type*} [Fintype ι] {j : ℕ} (l : ℕ)
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

private lemma trL_zero_local {j : ℕ} (A : (Fin j → Fin n) → ℝ) : trL 0 A = A := by
  funext w
  simp only [trL, Finset.univ_unique, Finset.sum_singleton]
  congr 1

private lemma aSq_zero_local (T : Tens n) (j : ℕ) :
    aSq n d T j 0 = frob (T j) / DD n d ^ j := by
  simp [aSq, trL_zero_local, cQ, Nat.factorial_ne_zero]
  ring

private lemma aT_frob_local (T : Tens n) (j l : ℕ) :
    frob (aT n d T j l) = aSq n d T j l := by
  classical
  have hp : (Real.sqrt (DD n d) ^ j) ^ 2 = DD n d ^ j := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, Real.sq_sqrt (by unfold DD; positivity)]
  unfold frob aT aSq
  simp only [mul_pow, div_pow, hp]
  rw [← Finset.mul_sum]
  rfl

private lemma aSq_trace_le_local (T : Tens n) (j l : ℕ) (hl : 2 * l ≤ j) :
    aSq n d T j l ≤ (cQ j l : ℝ) ^ 2 * (n : ℝ) ^ l * aSq n d T j 0 := by
  have h := trace_frob_le_local l hl (T j)
  simp only [Fintype.card_fin] at h
  rw [aSq_zero_local]
  unfold aSq
  have hD : 0 ≤ DD n d := by unfold DD; positivity
  have hh := mul_le_mul_of_nonneg_left h
    (by positivity : 0 ≤ (cQ j l : ℝ) ^ 2 / DD n d ^ j)
  convert hh using 1 <;> ring

private lemma weighted_trace_le_local (hn : 1 ≤ n) (k : ℕ) (T : Tens n) (j l : ℕ)
    (hj : j ∈ Finset.Icc 1 k) (hl : 2 * l ≤ j) (C : ℝ) (hC : 0 ≤ C) :
    C * aSq n d T j l / (n : ℝ) ^ (k - (j - 2 * l)) ≤
      (C * (cQ j l : ℝ) ^ 2 / ((j.factorial : ℝ) * j * (n : ℝ) ^ l)) * tj n d k T j := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hj
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hfac : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have he : k - (j - 2 * l) = (k - j) + l + l := by omega
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (aSq_trace_le_local (d := d) T j l hl) hC)
    (by positivity : 0 ≤ (n : ℝ) ^ (k - (j - 2 * l)))
  refine hh.trans_eq ?_
  rw [he, pow_add, pow_add]
  unfold tj
  field_simp
  <;> ring

private lemma maxJ_nonneg_local (k : ℕ) (g : ℕ → ℝ) : 0 ≤ maxJ k g := by
  unfold maxJ
  generalize ((List.range' 1 k).map g) = xs
  induction xs with
  | nil => simp
  | cons x xs ih => exact le_trans ih (le_max_right _ _)

private lemma le_maxJ_local (k : ℕ) (g : ℕ → ℝ) (j : ℕ) (hj : j ∈ Finset.Icc 1 k) :
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

private lemma frob_cast_local (s l : ℕ) (A : (Fin (s + 2 * l - 2 * l) → Fin n) → ℝ) :
    frob (fun w : Fin s → Fin n => A (fun t => w ⟨t.val, by have := t.isLt; omega⟩)) = frob A := by
  classical
  let e : (Fin s → Fin n) ≃ (Fin (s + 2 * l - 2 * l) → Fin n) :=
    Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl _)
  exact e.sum_comp (fun w => A w ^ 2)

private lemma frob_sum_error_local {ι : Type*} [Fintype ι] {a : ℕ} (η : ℝ) (hη : 0 < η)
    (L : Finset ℕ) (A B : (Fin a → ι) → ℝ) (C : ℕ → (Fin a → ι) → ℝ)
    (hA : ∀ w, A w = B w - ∑ l ∈ L, C l w) :
    frob A ≤ (1 + η) * frob B + (1 + 1 / η) * L.card * ∑ l ∈ L, frob (C l) := by
  classical
  have hy (b r : ℝ) : (b - r) ^ 2 ≤ (1 + η) * b ^ 2 + (1 + 1 / η) * r ^ 2 := by
    apply (mul_le_mul_iff_right₀ hη).mp
    have he : η * (1 + 1 / η) = η + 1 := by field_simp
    rw [mul_add, ← mul_assoc η (1 + 1 / η), he]
    nlinarith only [sq_nonneg (η * b + r)]
  unfold frob
  calc
    _ ≤ ∑ w, ((1 + η) * B w ^ 2 + (1 + 1 / η) * (L.card : ℝ) * (∑ l ∈ L, C l w ^ 2)) := by
      apply Finset.sum_le_sum
      intro w hw
      rw [hA]
      have hc := Finset.sum_mul_sq_le_sq_mul_sq L (fun _ => (1 : ℝ)) (fun l => C l w)
      simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
      have hh := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 1 + 1 / η)
      have hh' : (1 + 1 / η) * (∑ l ∈ L, C l w) ^ 2 ≤
          (1 + 1 / η) * (L.card : ℝ) * (∑ l ∈ L, C l w ^ 2) := by
        convert hh using 1 <;> ring
      exact (hy _ _).trans (add_le_add le_rfl hh')
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]

private lemma cascade_reindex_local (k : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ s ∈ Finset.Icc 1 k, ∑ l ∈ Finset.Icc 1 (Ls k s), F s l) =
      ∑ j ∈ Finset.Icc 1 k, ∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j),
        F (j - 2 * l) l := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun (i : Σ _ : ℕ, ℕ) _ => (⟨i.1 + 2 * i.2, i.2⟩ : Σ _ : ℕ, ℕ))
  · intro i hi
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, Ls] at *
    omega
  · intro i hi i' hi' he
    cases i with
    | mk s l =>
      cases i' with
      | mk s' l' =>
        have h1 := congrArg Sigma.fst he
        have h2 := congrArg (fun x : Σ _ : ℕ, ℕ => x.2) he
        dsimp only at h1 h2
        congr 1 <;> omega
  · intro i hi
    refine ⟨⟨i.1 - 2 * i.2, i.2⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, Ls] at *
      omega
    · have hi' := hi
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hi'
      apply Sigma.ext (by dsimp only; omega)
      rfl
  · intro i hi
    change F i.1 i.2 = F (i.1 + 2 * i.2 - 2 * i.2) i.2
    simp only [Nat.add_sub_cancel_right]

private lemma tj_nonneg_local (k : ℕ) (T : Tens n) (j : ℕ) : 0 ≤ tj n d k T j := by
  unfold tj aSq frob
  have hD : 0 ≤ DD n d := by unfold DD; positivity
  positivity

private lemma Nn_trace_bound_local (hn : 1 ≤ n) (k : ℕ) (T : Tens n) :
    Nn n d k T ≤ rhoBar n k * ∑ j ∈ Finset.Icc 1 k, tj n d k T j := by
  classical
  have hex : Nn n d k T = ∑ j ∈ Finset.Icc 1 k,
      ∑ l ∈ (Finset.range (k + 1)).filter (fun l => 2 * l < j),
        ((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * 4 ^ l * aSq n d T j l /
          (n : ℝ) ^ (k - (j - 2 * l)) := by
    simp only [Nn, levels, Finset.sum_filter, Finset.sum_product]
  rw [hex, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hset : (Finset.range (k + 1)).filter (fun l => 2 * l < j) =
      insert 0 ((Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    have := Finset.mem_Icc.mp hj
    omega
  rw [hset, Finset.sum_insert (by simp)]
  simp only [Nat.mul_zero, Nat.sub_zero, pow_zero, mul_one]
  change tj n d k T j + _ ≤ _
  have ht := tj_nonneg_local (d := d) k T j
  let G : ℕ → ℝ := fun l => ((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * 4 ^ l *
    (cQ j l : ℝ) ^ 2 / ((j.factorial : ℝ) * j * (n : ℝ) ^ l)
  have hh : (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j),
      ((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * 4 ^ l * aSq n d T j l /
        (n : ℝ) ^ (k - (j - 2 * l))) ≤
      (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j), G l) * tj n d k T j := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro l hl
    exact weighted_trace_le_local hn k T j l hj (by have := (Finset.mem_filter.mp hl).2; omega)
      _ (by positivity)
  have hm : 1 + (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j), G l) ≤ rhoBar n k :=
    by
      exact le_maxJ_local k (fun j => 1 + ∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j),
        ((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * 4 ^ l * (cQ j l : ℝ) ^ 2 /
          ((j.factorial : ℝ) * j * (n : ℝ) ^ l)) j hj
  calc
    _ ≤ tj n d k T j + (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j), G l) * tj n d k T j :=
      add_le_add le_rfl hh
    _ = (1 + (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j), G l)) * tj n d k T j := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hm ht

private lemma bEff_decompose_local (q : ℝ) (k : ℕ) (T : Tens n) (s : ℕ) (hs : s ∈ Finset.Icc 1 k)
    (hν0 : q ^ 0 = 1) (w : Fin s → Fin n) :
    aT n d T s 0 w = bq n d k T s q w - ∑ l ∈ Finset.Icc 1 (Ls k s),
      q ^ l * aT n d T (s + 2 * l) l (fun t => w ⟨t.val, by have := t.isLt; omega⟩) := by
  classical
  have hset : (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k) =
      insert 0 (Finset.Icc 1 (Ls k s)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_Icc, Ls]
    have := Finset.mem_Icc.mp hs
    omega
  unfold bq
  rw [hset, Finset.sum_insert (by simp), hν0]
  simp only [Nat.mul_zero, Nat.add_zero, one_mul]
  rw [add_sub_cancel_right]
  congr 1

private lemma cascade_level_local (q : ℝ) (hn : 1 ≤ n) (k : ℕ) (T : Tens n) (η : ℝ) (hη : 0 < η)
    (s : ℕ) (hs : s ∈ Finset.Icc 1 k) (hν0 : q ^ 0 = 1)
    (hν : ∀ l ∈ Finset.Icc 1 (Ls k s), 0 ≤ q ^ l ∧ q ^ l ≤ ((d : ℝ) + 1) ^ l) :
    tj n d k T s ≤ (1 + η) * ((s.factorial : ℝ) * s * frob (bq n d k T s q) / (n : ℝ) ^ (k - s)) +
      (1 + 1 / η) * ∑ l ∈ Finset.Icc 1 (Ls k s),
        (Ls k s : ℝ) * ((s.factorial : ℝ) * s * ((d : ℝ) + 1) ^ (2 * l) *
          (cQ (s + 2 * l) l : ℝ) ^ 2 / (((s + 2 * l).factorial : ℝ) * (s + 2 * l))) /
          (n : ℝ) ^ l * tj n d k T (s + 2 * l) := by
  classical
  let C : ℕ → (Fin s → Fin n) → ℝ := fun l w => q ^ l *
    aT n d T (s + 2 * l) l (fun t => w ⟨t.val, by have := t.isLt; omega⟩)
  have hC (l : ℕ) : frob (C l) = (q ^ l) ^ 2 * aSq n d T (s + 2 * l) l := by
    unfold C frob
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    rw [← aT_frob_local, ← frob_cast_local s l]
    rfl
  have hCs (l : ℕ) (hl : l ∈ Finset.Icc 1 (Ls k s)) :
      frob (C l) ≤ ((d : ℝ) + 1) ^ (2 * l) * aSq n d T (s + 2 * l) l := by
    rw [hC]
    have hp := pow_le_pow_left₀ (hν l hl).1 (hν l hl).2 2
    have he : (((d : ℝ) + 1) ^ l) ^ 2 = ((d : ℝ) + 1) ^ (2 * l) := by rw [← pow_mul, Nat.mul_comm l 2]
    rw [he] at hp
    apply mul_le_mul_of_nonneg_right hp
    unfold aSq frob
    have hD : 0 ≤ DD n d := by unfold DD; positivity
    positivity
  have hA := frob_sum_error_local η hη (Finset.Icc 1 (Ls k s))
    (aT n d T s 0) (bq n d k T s q) C (bEff_decompose_local q k T s hs hν0)
  rw [aT_frob_local, Nat.card_Icc] at hA
  simp only [Nat.add_sub_cancel] at hA
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let W : ℝ := (s.factorial : ℝ) * s / (n : ℝ) ^ (k - s)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have h := mul_le_mul_of_nonneg_left hA hW
  have ht : W * aSq n d T s 0 = tj n d k T s := by dsimp [W, tj]; ring
  rw [ht] at h
  refine h.trans ?_
  have hsum : W * ∑ l ∈ Finset.Icc 1 (Ls k s), frob (C l) ≤
      ∑ l ∈ Finset.Icc 1 (Ls k s),
        ((s.factorial : ℝ) * s * ((d : ℝ) + 1) ^ (2 * l) * (cQ (s + 2 * l) l : ℝ) ^ 2 /
          (((s + 2 * l).factorial : ℝ) * (s + 2 * l) * (n : ℝ) ^ l)) * tj n d k T (s + 2 * l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    have hj : s + 2 * l ∈ Finset.Icc 1 k := by
      simp only [Finset.mem_Icc, Ls] at *
      omega
    have htr := weighted_trace_le_local (d := d) hn k T (s + 2 * l) l hj (by omega)
      ((s.factorial : ℝ) * s * ((d : ℝ) + 1) ^ (2 * l)) (by positivity)
    simp only [Nat.add_sub_cancel_right] at htr
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at htr
    have hh := mul_le_mul_of_nonneg_left (hCs l hl) hW
    refine hh.trans ?_
    convert htr using 1 <;> (try dsimp [W]) <;> ring
  have hh := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ (1 + 1 / η) * (Ls k s : ℝ))
  have he : W * ((1 + η) * frob (bq n d k T s q) +
      (1 + 1 / η) * (Ls k s : ℝ) * ∑ l ∈ Finset.Icc 1 (Ls k s), frob (C l)) =
      (1 + η) * ((s.factorial : ℝ) * s * frob (bq n d k T s q) / (n : ℝ) ^ (k - s)) +
      ((1 + 1 / η) * (Ls k s : ℝ)) * (W * ∑ l ∈ Finset.Icc 1 (Ls k s), frob (C l)) := by
    dsimp [W]; ring
  rw [he]
  refine (add_le_add le_rfl hh).trans_eq ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  field_simp
  <;> ring


/-- **Lemma F′** (the cascade, pointwise in `q ∈ [0, d+1]`). -/
theorem cascade43 (hn : 1 ≤ n) (k : ℕ) (T : Tens n) (η : ℝ) (hη : 0 < η)
    (hθ : (1 + 1 / η) * thetaT n d k < 1) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ (d : ℝ) + 1) :
    Nn n d k T ≤ Kc n d k η *
      ∑ s ∈ Finset.Icc 1 k, (s.factorial : ℝ) * s * frob (bq n d k T s q) / (n : ℝ) ^ (k - s) := by
  classical
  let B : ℝ := ∑ s ∈ Finset.Icc 1 k,
    (s.factorial : ℝ) * s * frob (bq n d k T s q) / (n : ℝ) ^ (k - s)
  let V : ℝ := ∑ j ∈ Finset.Icc 1 k, tj n d k T j
  let E : ℕ → ℕ → ℝ := fun s l => (Ls k s : ℝ) *
    ((s.factorial : ℝ) * s * ((d : ℝ) + 1) ^ (2 * l) * (cQ (s + 2 * l) l : ℝ) ^ 2 /
      (((s + 2 * l).factorial : ℝ) * (s + 2 * l))) / (n : ℝ) ^ l * tj n d k T (s + 2 * l)
  have hlevel (s : ℕ) (hs : s ∈ Finset.Icc 1 k) : tj n d k T s ≤
      (1 + η) * ((s.factorial : ℝ) * s * frob (bq n d k T s q) / (n : ℝ) ^ (k - s)) +
        (1 + 1 / η) * ∑ l ∈ Finset.Icc 1 (Ls k s), E s l := by
    apply cascade_level_local q hn k T η hη s hs (by simp)
    intro l hl
    have hl' := Finset.mem_Icc.mp hl
    exact ⟨pow_nonneg hq0 l, pow_le_pow_left₀ hq0 hq1 l⟩
  have herror : (∑ s ∈ Finset.Icc 1 k, ∑ l ∈ Finset.Icc 1 (Ls k s), E s l) ≤ thetaT n d k * V := by
    rw [cascade_reindex_local]
    dsimp [V]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have he : (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j), E (j - 2 * l) l) =
        (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j), (Ls k (j - 2 * l) : ℝ) *
          (((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * ((d : ℝ) + 1) ^ (2 * l) *
            (cQ j l : ℝ) ^ 2 / ((j.factorial : ℝ) * j)) / (n : ℝ) ^ l) * tj n d k T j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      have hl' := (Finset.mem_filter.mp hl).2
      dsimp [E]
      rw [Nat.sub_add_cancel (by omega : 2 * l ≤ j)]
      have hecast : (j - 2 * l : ℕ) + (2 : ℝ) * l = (j : ℝ) := by
        exact_mod_cast (Nat.sub_add_cancel (by omega : 2 * l ≤ j))
      rw [hecast]
    rw [he]
    apply mul_le_mul_of_nonneg_right _ (tj_nonneg_local k T j)
    unfold thetaT
    exact le_maxJ_local k (fun j => ∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j),
      (Ls k (j - 2 * l) : ℝ) * (((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) *
        ((d : ℝ) + 1) ^ (2 * l) * (cQ j l : ℝ) ^ 2 / ((j.factorial : ℝ) * j)) / (n : ℝ) ^ l) j hj
  have hv : V ≤ (1 + η) * B + (1 + 1 / η) * thetaT n d k * V := by
    have hh := Finset.sum_le_sum (s := Finset.Icc 1 k) hlevel
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hh
    refine hh.trans ?_
    dsimp [B]
    apply add_le_add le_rfl
    convert mul_le_mul_of_nonneg_left herror (by positivity : 0 ≤ 1 + 1 / η) using 1
    ring
  have hden : 0 < 1 - (1 + 1 / η) * thetaT n d k := by linarith
  have hmain : V ≤ (1 + η) / (1 - (1 + 1 / η) * thetaT n d k) * B := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hv]

  have hnorm := Nn_trace_bound_local (d := d) hn k T
  have hr : 0 ≤ rhoBar n k := maxJ_nonneg_local k _
  have hh := mul_le_mul_of_nonneg_left hmain hr
  refine hnorm.trans (hh.trans_eq ?_)
  unfold Kc
  dsimp [B]
  ring


end BstLean.Part43

