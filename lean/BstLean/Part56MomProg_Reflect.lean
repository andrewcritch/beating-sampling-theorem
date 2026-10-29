import BstLean.Part56MomProg_Index

/-! The Householder reflection sending `v` to a coordinate vector, and the reduction of every
surrogate weight to coefficients of a polynomial and one-dimensional tilted moments. -/

namespace BstLean.Part56.MomProg

open MeasureTheory MvPolynomial
open BstLean.Part56
open BstLean.Part29 (uniformSphere)

variable {n : ℕ}

/-- `u = v − e_a`. -/
noncomputable def uvec (a : Fin n) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun l => v l - if l = a then 1 else 0

/-- The reflection matrix `I − 2 u uᵀ/‖u‖²` (`I` when `u = 0`). -/
noncomputable def Rmat (a : Fin n) (v : Fin n → ℝ) (m l : Fin n) : ℝ :=
  (if m = l then 1 else 0) - 2 / (∑ i, uvec a v i ^ 2) * uvec a v m * uvec a v l

/-- The image `R x`. -/
noncomputable def Rapp (a : Fin n) (v x : Fin n → ℝ) : Fin n → ℝ :=
  fun m => ∑ l, Rmat a v m l * x l

theorem reflect_props (a : Fin n) (v : Fin n → ℝ) (hv : UnitV v) :
    (uniformSphere n).map (Rapp a v) = uniformSphere n ∧
      (∀ x, ∑ i, v i * Rapp a v x i = x a) := by
  classical
  let V : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single a 1
  let W : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (uvec a v)
  have hW : V - e = W := by
    ext l
    simp [V, e, W, uvec, EuclideanSpace.single_apply]
  have hV : ‖V‖ = 1 := by
    have h : ‖V‖ ^ 2 = 1 := by simpa [V, EuclideanSpace.real_norm_sq_eq, UnitV] using hv
    nlinarith [norm_nonneg V]
  have he : ‖e‖ = 1 := by simp [e]
  let R := (ℝ ∙ W)ᗮ.reflection
  have hRV : R V = e := by
    have := Submodule.reflection_sub (hV.trans he.symm)
    rw [hW] at this
    exact this
  have hRR (x) : R (R x) = x := R.symm_apply_apply x
  have hform (x : Fin n → ℝ) : WithLp.ofLp (R (WithLp.toLp 2 x)) = Rapp a v x := by
    have h1 : R (WithLp.toLp 2 x) = WithLp.toLp 2 x -
        (2 : ℝ) • (((ℝ ∙ W).starProjection (WithLp.toLp 2 x))) := by
      simp only [R, Submodule.reflection_orthogonal, LinearIsometryEquiv.trans_apply,
        LinearIsometryEquiv.coe_neg, Submodule.reflection_apply]
      simp only [neg_sub, two_smul]
    rw [h1, Submodule.starProjection_singleton]
    ext m
    simp only [Rapp, Rmat, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, W, PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have : ∑ l, 2 / (∑ i, uvec a v i ^ 2) * uvec a v m * uvec a v l * x l =
        2 / (∑ i, uvec a v i ^ 2) * uvec a v m * ∑ l, x l * uvec a v l := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
    rw [this]
    have hi : ∀ l, inner ℝ (uvec a v l) (x l) = x l * uvec a v l := fun l => by
      simp [mul_comm]
    simp only [hi, RCLike.ofReal_real_eq_id, id]
    ring
  constructor
  · have hm := uniformSphere_involution R hRR
    have hfun : (fun x => WithLp.ofLp (R (WithLp.toLp 2 x))) = Rapp a v := funext hform
    rw [hfun] at hm
    exact hm
  · intro x
    have h := R.inner_map_map V (R (WithLp.toLp 2 x))
    rw [hRV, hRR] at h
    rw [← hform]
    simpa [e, V, PiLp.inner_apply, mul_comm] using h.symm

theorem Rapp_continuous (a : Fin n) (v : Fin n → ℝ) : Continuous (Rapp a v) := by
  unfold Rapp; fun_prop

/-- The linear forms `L_m = Σ_l R_{ml} X_l`. -/
noncomputable def Lform (a : Fin n) (v : Fin n → ℝ) (m : Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ l, C (Rmat a v m l) * X l

theorem eval_Lform (a : Fin n) (v x : Fin n → ℝ) (m : Fin n) :
    eval x (Lform a v m) = Rapp a v x m := by
  simp [Lform, Rapp]

theorem eval_bind_Lform (a : Fin n) (v x : Fin n → ℝ) (P : MvPolynomial (Fin n) ℝ) :
    eval x (bind₁ (Lform a v) P) = eval (Rapp a v x) P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, eval_Lform]

theorem totalDegree_Lform (a : Fin n) (v : Fin n → ℝ) (m : Fin n) :
    (Lform a v m).totalDegree ≤ 1 := by
  unfold Lform
  apply totalDegree_finsetSum_le
  intro l _
  apply (totalDegree_mul _ _).trans
  simp [totalDegree_X]

theorem totalDegree_bind_linear (L : Fin n → MvPolynomial (Fin n) ℝ)
    (hL : ∀ m, (L m).totalDegree ≤ 1) (P : MvPolynomial (Fin n) ℝ) :
    (bind₁ L P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro μ hμ
  rw [bind₁_monomial]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  have h1 : ∑ i ∈ μ.support, (L i ^ μ i).totalDegree ≤ ∑ i ∈ μ.support, μ i := by
    apply Finset.sum_le_sum
    intro i _
    exact (totalDegree_pow _ _).trans (by nlinarith [hL i])
  apply h1.trans
  have := le_totalDegree hμ
  simpa [Finsupp.sum] using this

/-! ## Moments -/

/-- `x^μ = Π_{l ∈ supp μ} x_l^{μ_l}`. -/
noncomputable def xpow (x : Fin n → ℝ) (μ : Fin n →₀ ℕ) : ℝ := ∏ l ∈ μ.support, x l ^ μ l

theorem monoVal_toMultiset (x : Fin n → ℝ) (μ : Fin n →₀ ℕ) :
    BstLean.Part36.monoVal x (Finsupp.toMultiset μ) = xpow x μ := by
  classical
  induction μ using Finsupp.induction with
  | zero => simp [BstLean.Part36.monoVal, xpow]
  | single_add l e f hl he ih =>
    have hsupp : (Finsupp.single l e + f).support = insert l f.support := by
      rw [Finsupp.support_add_eq, Finsupp.support_single_ne_zero _ he]
      · rfl
      · rw [Finsupp.support_single_ne_zero _ he]
        simpa using hl
    unfold xpow at ih ⊢
    rw [map_add, BstLean.Part36.monoVal, Multiset.map_add, Multiset.prod_add, hsupp,
      Finset.prod_insert hl]
    rw [BstLean.Part36.monoVal] at ih
    rw [ih]
    have hfl : f l = 0 := Finsupp.notMem_support_iff.mp hl
    simp only [Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.map_singleton,
      Multiset.prod_nsmul, Multiset.prod_singleton, Finsupp.add_apply, Finsupp.single_eq_same,
      hfl, add_zero]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have : i ≠ l := fun h => hl (h ▸ hi)
    simp [Finsupp.single_eq_of_ne this]

/-- The tilted moments `m(i, μ) = E_σ[x_a^{2i} x^μ]`. -/
noncomputable def momA (a : Fin n) (i : ℕ) (μ : Fin n →₀ ℕ) : ℝ :=
  ∫ x, x a ^ (2 * i) * xpow x μ ∂uniformSphere n

theorem xpow_continuous (μ : Fin n →₀ ℕ) : Continuous (fun x : Fin n → ℝ => xpow x μ) := by
  unfold xpow; fun_prop

/-- The table `T(μ) = Σ_{i ≤ K} t^i/i! · m(i, μ)`. -/
noncomputable def Ttab (a : Fin n) (K : ℕ) (t : ℝ) (μ : Fin n →₀ ℕ) : ℝ :=
  ∑ i ∈ Finset.range (K + 1), t ^ i / (i.factorial : ℝ) * momA a i μ

theorem integral_poly_tilt (hn : 1 ≤ n) (a : Fin n) (K : ℕ) (t : ℝ)
    (Q : MvPolynomial (Fin n) ℝ) :
    (∫ x, eval x Q * BstLean.Part37.taylorExp K (t * x a ^ 2) ∂uniformSphere n) =
      ∑ μ ∈ Q.support, Q.coeff μ * Ttab a K t μ := by
  have hint : ∀ μ i, Integrable (fun x : Fin n → ℝ => x a ^ (2 * i) * xpow x μ)
      (uniformSphere n) := fun μ i =>
    sphere_integrable hn (by have := xpow_continuous μ; fun_prop)
  have hexp : ∀ x : Fin n → ℝ, eval x Q * BstLean.Part37.taylorExp K (t * x a ^ 2) =
      ∑ μ ∈ Q.support, ∑ i ∈ Finset.range (K + 1),
        Q.coeff μ * (t ^ i / (i.factorial : ℝ)) * (x a ^ (2 * i) * xpow x μ) := by
    intro x
    rw [eval_eq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro μ _
    unfold BstLean.Part37.taylorExp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold xpow
    rw [mul_pow, ← pow_mul]
    ring
  simp_rw [hexp]
  rw [integral_finset_sum _ (fun μ _ => integrable_finset_sum _
    (fun i _ => (hint μ i).const_mul _))]
  apply Finset.sum_congr rfl
  intro μ _
  rw [integral_finset_sum _ (fun i _ => (hint μ i).const_mul _)]
  unfold Ttab
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, momA]
  ring

/-- Restriction of a support sum to the index of degree `≤ D`. -/
theorem sum_support_Idx {D : ℕ} (Q : MvPolynomial (Fin n) ℝ) (hQ : Q.totalDegree ≤ D)
    (g : (Fin n →₀ ℕ) → ℝ) :
    ∑ μ ∈ Q.support, Q.coeff μ * g μ = ∑ μ : Idx n D, Q.coeff μ.1 * g μ.1 := by
  classical
  let emb : Idx n D ↪ (Fin n →₀ ℕ) := ⟨Subtype.val, Subtype.val_injective⟩
  rw [show (∑ μ : Idx n D, Q.coeff μ.1 * g μ.1) = ∑ ν ∈ Finset.univ.map emb, Q.coeff ν * g ν
    from (Finset.sum_map Finset.univ emb (fun ν => Q.coeff ν * g ν)).symm]
  apply Finset.sum_subset
  · intro μ hμ
    rw [Finset.mem_map]
    refine ⟨⟨μ, ?_⟩, Finset.mem_univ _, rfl⟩
    have := le_totalDegree hμ
    exact this.trans hQ
  · intro μ _ hμ
    rw [MvPolynomial.notMem_support_iff.mp hμ, zero_mul]

end BstLean.Part56.MomProg
