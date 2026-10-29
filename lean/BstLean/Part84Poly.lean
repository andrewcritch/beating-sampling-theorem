import BstLean.Part84Defs

/-!
# Part 84, `Poly`: `F_x` and `B` are polynomials in `W`; `B` and `V` are polynomials in the scale

`polyRep : PolyRep n d` and `radPoly : RadPoly n d` (for `1 ≤ n`).

Method. For a family `L x i` of polynomials of degree `≤ 1` in variables `τ` whose coefficients are
continuous in `x`, the substitution `aeval (L x) P` has degree `≤ deg P` and coefficients continuous
in `x`. All its exponents lie in the finite set of exponents of degree `≤ K`, so that the integral
over the sphere is taken coefficient by coefficient (`core`).
-/

namespace BstLean.Part84

open MeasureTheory MvPolynomial
open BstLean.Part29 (uniformSphere)
open BstLean.Part41 (varU)
open BstLean.Part78 (zv sph_int)
open BstLean.Part81 (JJ WIdx pf)

section gen

variable {σ τ α : Type*}

lemma totalDegree_finset_sum_le {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial τ ℝ} {K : ℕ}
    (h : ∀ i ∈ s, (f i).totalDegree ≤ K) : (s.sum f).totalDegree ≤ K :=
  (totalDegree_finsetSum s f).trans (Finset.sup_le h)

/-- Substitution of polynomials of degree `≤ 1` does not raise the degree. -/
lemma deg_aeval (L : σ → MvPolynomial τ ℝ) (hL : ∀ i, (L i).totalDegree ≤ 1)
    (P : MvPolynomial σ ℝ) : (aeval L P).totalDegree ≤ P.totalDegree := by
  rw [aeval_def, eval₂_eq]
  refine totalDegree_finset_sum_le (fun m hm => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  unfold Finsupp.sum
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine (totalDegree_pow _ _).trans ?_
  calc m i * (L i).totalDegree ≤ m i * 1 := Nat.mul_le_mul_left _ (hL i)
    _ = m i := mul_one _

/-- The coefficients of the substitution are continuous in the parameter. -/
lemma cont_coeff [TopologicalSpace α] (L : α → σ → MvPolynomial τ ℝ)
    (hL : ∀ i m, Continuous fun x => (L x i).coeff m) (P : MvPolynomial σ ℝ) :
    ∀ m, Continuous fun x => (aeval (L x) P).coeff m := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro m
    simp only [aeval_C, algebraMap_eq]
    exact continuous_const
  | add p q hp hq =>
    intro m
    simp only [map_add, AddMonoidAlgebra.coeff_add]
    exact (hp m).add (hq m)
  | mul_X p i hp =>
    intro m
    simp only [map_mul, aeval_X, coeff_mul]
    exact continuous_finsetSum _ (fun a _ => (hp a.1).mul (hL i a.2))

lemma eval_aeval' (L : σ → MvPolynomial τ ℝ) (W : τ → ℝ) (P : MvPolynomial σ ℝ) :
    eval W (aeval L P) = eval (fun i => eval W (L i)) P := by
  exact eval₂Hom_bind₁ (RingHom.id ℝ) W L P

/-- Coefficientwise integration of a substitution. -/
lemma core [Finite τ] {n : ℕ} (hn : 1 ≤ n) (L : (Fin n → ℝ) → σ → MvPolynomial τ ℝ)
    (hLd : ∀ x i, (L x i).totalDegree ≤ 1)
    (hLc : ∀ i m, Continuous fun x => (L x i).coeff m)
    (K : ℕ) (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ K) :
    ∃ (S : Finset (τ →₀ ℕ)) (c : (τ →₀ ℕ) → ℝ),
      (∀ m ∈ S, (m.sum fun _ e => e) ≤ K) ∧
      (∀ W : τ → ℝ, Continuous fun x => eval W (aeval (L x) P)) ∧
      ∀ W : τ → ℝ, ∫ x, eval W (aeval (L x) P) ∂uniformSphere n =
        ∑ m ∈ S, c m * ∏ i ∈ m.support, W i ^ m i := by
  classical
  have hfin : {m : τ →₀ ℕ | (m.sum fun _ e => e) ≤ K}.Finite := by
    have := Finsupp.finite_of_degree_le (σ := τ) K
    refine this.subset (fun m hm => ?_)
    simpa [Finsupp.degree_apply, Finsupp.sum] using hm
  have hcc := cont_coeff L hLc P
  have hev : ∀ (W : τ → ℝ) x, eval W (aeval (L x) P) =
      ∑ m ∈ hfin.toFinset, (aeval (L x) P).coeff m * ∏ i ∈ m.support, W i ^ m i := by
    intro W x
    rw [eval_eq]
    refine Finset.sum_subset (fun m hm => ?_) (fun m _ hm => ?_)
    · rw [Set.Finite.mem_toFinset]
      exact (le_totalDegree hm).trans ((deg_aeval _ (hLd x) P).trans hP)
    · rw [notMem_support_iff.mp hm, zero_mul]
  refine ⟨hfin.toFinset, fun m => ∫ x, (aeval (L x) P).coeff m ∂uniformSphere n, ?_, ?_, ?_⟩
  · intro m hm
    exact hfin.mem_toFinset.mp hm
  · intro W
    simp only [hev]
    exact continuous_finsetSum _ (fun m _ => (hcc m).mul continuous_const)
  · intro W
    simp only [hev]
    rw [integral_finsetSum _ (fun m _ => (sph_int hn (hcc m)).mul_const _)]
    exact Finset.sum_congr rfl (fun m _ => integral_mul_const _ _)

end gen

variable {n d : ℕ}

/-! ## `PolyRep` -/

/-- The linear forms `W ↦ lam · (W p(x))_i`. -/
noncomputable def LW (n d : ℕ) (lam : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    MvPolynomial (WIdx n d) ℝ :=
  C lam * ∑ q : JJ n d, C (pf x q) * X (q, i)

lemma LW_deg (lam : ℝ) (x : Fin n → ℝ) (i : Fin n) : (LW n d lam x i).totalDegree ≤ 1 := by
  unfold LW
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine totalDegree_finset_sum_le (fun q _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_X _).le

lemma LW_cont (lam : ℝ) (i : Fin n) (m : WIdx n d →₀ ℕ) :
    Continuous fun x : Fin n → ℝ => (LW n d lam x i).coeff m := by
  unfold LW
  simp only [coeff_C_mul, coeff_sum]
  exact continuous_const.mul
    (continuous_finsetSum _ (fun q _ => (BstLean.Part81.cont_pf q).mul continuous_const))

lemma LW_eval (lam : ℝ) (x : Fin n → ℝ) (P : MvPolynomial (Fin n) ℝ) (W : WIdx n d → ℝ) :
    eval W (aeval (LW n d lam x) P) = FW P lam W x := by
  rw [eval_aeval']
  unfold FW LW zv
  simp [mul_comm]

/-- From a coefficient expansion to a polynomial of degree `≤ K`. -/
lemma mv_of_expansion {τ : Type*} (K : ℕ) (S : Finset (τ →₀ ℕ)) (c : (τ →₀ ℕ) → ℝ)
    (hS : ∀ m ∈ S, (m.sum fun _ e => e) ≤ K) :
    ∃ Q : MvPolynomial τ ℝ, Q.totalDegree ≤ K ∧
      ∀ W : τ → ℝ, eval W Q = ∑ m ∈ S, c m * ∏ i ∈ m.support, W i ^ m i := by
  refine ⟨∑ m ∈ S, monomial m (c m), ?_, ?_⟩
  · refine totalDegree_finset_sum_le (fun m hm => ?_)
    exact (totalDegree_monomial_le _ _).trans (hS m hm)
  · intro W
    rw [map_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [eval_monomial]
    rfl

theorem polyRep (n d : ℕ) (hn : 1 ≤ n) : PolyRep n d := by
  intro K P hP lam
  constructor
  · intro x
    refine ⟨aeval (LW n d lam x) P, (deg_aeval _ (LW_deg lam x) P).trans hP, ?_⟩
    intro W
    exact LW_eval lam x P W
  · obtain ⟨S, c, hS, -, hI⟩ := core hn (LW n d lam) (LW_deg lam) (LW_cont lam) K P hP
    obtain ⟨Q, hQ, hQe⟩ := mv_of_expansion K S c hS
    refine ⟨Q, hQ, fun W => ?_⟩
    rw [hQe, ← hI]
    unfold BW
    simp only [LW_eval]

/-! ## `RadPoly` -/

/-- The linear forms `lam ↦ lam · (W p(x))_i`, in one variable. -/
noncomputable def LR (W : WIdx n d → ℝ) (x : Fin n → ℝ) (i : Fin n) : MvPolynomial Unit ℝ :=
  C (zv W (pf x) i) * X ()

lemma LR_deg (W : WIdx n d → ℝ) (x : Fin n → ℝ) (i : Fin n) : (LR W x i).totalDegree ≤ 1 := by
  unfold LR
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_X _).le

lemma LR_cont (W : WIdx n d → ℝ) (i : Fin n) (m : Unit →₀ ℕ) :
    Continuous fun x : Fin n → ℝ => (LR W x i).coeff m := by
  unfold LR zv
  simp only [coeff_C_mul]
  exact (continuous_finsetSum _
    (fun q _ => continuous_const.mul (BstLean.Part81.cont_pf q))).mul continuous_const

lemma LR_eval (W : WIdx n d → ℝ) (x : Fin n → ℝ) (P : MvPolynomial (Fin n) ℝ) (lam : ℝ) :
    eval (fun _ : Unit => lam) (aeval (LR W x) P) = FW P lam W x := by
  rw [eval_aeval']
  unfold FW LR
  have : (fun i => eval (fun _ : Unit => lam) (C (zv W (pf x) i) * X ())) =
      fun i => lam * zv W (pf x) i := by
    funext i
    simp [mul_comm]
  rw [this]

lemma cont_FW (P : MvPolynomial (Fin n) ℝ) (lam : ℝ) (W : WIdx n d → ℝ) (hn : 1 ≤ n) :
    Continuous (FW P lam W) := by
  obtain ⟨S, c, -, hC, -⟩ := core hn (LR W) (LR_deg W) (LR_cont W) _ P le_rfl
  have := hC (fun _ => lam)
  simp only [LR_eval] at this
  exact this

/-- `B` is a polynomial in the scale. -/
lemma radB (hn : 1 ≤ n) (K : ℕ) (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ K)
    (W : WIdx n d → ℝ) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ K ∧ ∀ lam : ℝ, q.eval lam = BW P lam W := by
  obtain ⟨S, c, hS, -, hI⟩ := core hn (LR W) (LR_deg W) (LR_cont W) K P hP
  refine ⟨∑ m ∈ S, Polynomial.C (c m) * Polynomial.X ^ (m ()), ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun m hm => ?_)
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    refine le_trans ?_ (hS m hm)
    unfold Finsupp.sum
    by_cases h : m () = 0
    · rw [h]; exact Nat.zero_le _
    · exact Finset.single_le_sum (f := fun i => m i) (fun _ _ => Nat.zero_le _)
        (Finsupp.mem_support_iff.mpr h)
  · intro lam
    have h := hI (fun _ => lam)
    simp only [LR_eval] at h
    unfold BW
    rw [h, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    congr 1
    by_cases h0 : m () = 0
    · have : m.support = ∅ := by
        ext i; cases i; simp [h0]
      rw [this, h0]; simp
    · have : m.support = {()} := by
        ext i; cases i; simp [h0]
      rw [this]; simp

lemma VW_eq (hn : 1 ≤ n) (P : MvPolynomial (Fin n) ℝ) (lam : ℝ) (W : WIdx n d → ℝ) :
    VW P lam W = BW (P * P) lam W - BW P lam W ^ 2 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hc := cont_FW (d := d) P lam W hn
  have h1 : Integrable (FW P lam W) (uniformSphere n) := sph_int hn hc
  have h2 : Integrable (fun x => FW P lam W x ^ 2) (uniformSphere n) := sph_int hn (hc.pow 2)
  have hsq : ∀ x, FW (P * P) lam W x = FW P lam W x ^ 2 := by
    intro x; unfold FW; rw [map_mul, sq]
  unfold VW varU BW
  simp only [hsq]
  set B := ∫ y, FW P lam W y ∂uniformSphere n with hB
  have e : ∀ x, (FW P lam W x - B) ^ 2 = FW P lam W x ^ 2 - 2 * B * FW P lam W x + B ^ 2 := by
    intro x; ring
  simp only [e]
  have e1 := integral_add (h2.sub (h1.const_mul (2 * B))) (integrable_const (μ := uniformSphere n) (B ^ 2))
  have e2 := integral_sub h2 (h1.const_mul (2 * B))
  have e3 := integral_const_mul (μ := uniformSphere n) (2 * B) (FW P lam W)
  simp only [Pi.sub_apply] at e1
  rw [e1, e2, e3, integral_const, ← hB]
  simp
  ring

theorem radPoly (n d : ℕ) (hn : 1 ≤ n) : RadPoly n d := by
  intro K P hP W
  obtain ⟨q1, hq1, he1⟩ := radB (d := d) hn K P hP W
  refine ⟨⟨q1, hq1, he1⟩, ?_⟩
  have hPP : (P * P).totalDegree ≤ 2 * K := by
    refine (totalDegree_mul _ _).trans ?_
    omega
  obtain ⟨q2, hq2, he2⟩ := radB (d := d) hn (2 * K) (P * P) hPP W
  refine ⟨q2 - q1 ^ 2, ?_, ?_⟩
  · refine (Polynomial.natDegree_sub_le _ _).trans (max_le hq2 ?_)
    refine Polynomial.natDegree_pow_le.trans ?_
    exact Nat.mul_le_mul_left 2 hq1
  · intro lam
    rw [Polynomial.eval_sub, Polynomial.eval_pow, he1, he2, VW_eq hn]

end BstLean.Part84
