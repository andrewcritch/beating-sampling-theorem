import BstLean.Part78SharpMom

/-!
# Part 78 (sharp): the feature operator bound with constant `1`, and the exact value of `ss2`

* `featOp1 : FeatOp n 1`, that is `E (c·p(x))² ≤ ‖c‖²/n` for the non-constant raw monomials of
  degree `≤ 2` under the uniform distribution on the sphere.
* `kap_formula' : κ(x,y) = s + (s² + P)/2`, `s = Σ x_i y_i`, `P = Σ x_i² y_i²`.
* `ss2_exact : ss2 n = 1/n + (3n + 15)/(2n(n+2)²)`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part78

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part41 (Mono phiM)

variable {n : ℕ}

/-- The symmetric matrix of the quadratic part of a coefficient vector. -/
noncomputable def matOf (c : Mono n 2 → ℝ) (i j : Fin n) : ℝ :=
  (c (quadQ s(i, j)) + if i = j then c (quadQ s(i, i)) else 0) / 2

lemma int_sq (hn : 1 ≤ n) (a : Fin n → ℝ) (A : Fin n → Fin n → ℝ) :
    ∫ x, (linF a x + quadF A x) ^ 2 ∂uniformSphere n =
      (∑ i, a i * a i) / n +
        ((∑ i, A i i) * (∑ i, A i i) + ∑ i, ∑ j, A i j * A i j + ∑ i, ∑ j, A i j * A j i) /
          ((n : ℝ) * (n + 2)) := by
  have hL := continuous_linF a
  have hQ := continuous_quadF A
  have e : ∀ x : Fin n → ℝ, (linF a x + quadF A x) ^ 2 =
      linF a x * linF a x + 2 * (linF a x * quadF A x) + quadF A x * quadF A x := by
    intro x; ring
  simp_rw [e]
  have iLL : Integrable (fun x => linF a x * linF a x) (uniformSphere n) :=
    sphere_cont_integrable' hn (hL.mul hL)
  have iLQ : Integrable (fun x => 2 * (linF a x * quadF A x)) (uniformSphere n) :=
    sphere_cont_integrable' hn (continuous_const.mul (hL.mul hQ))
  have iQQ : Integrable (fun x => quadF A x * quadF A x) (uniformSphere n) :=
    sphere_cont_integrable' hn (hQ.mul hQ)
  have iS : Integrable (fun x => linF a x * linF a x + 2 * (linF a x * quadF A x))
      (uniformSphere n) := iLL.add iLQ
  rw [integral_add iS iQQ, integral_add iLL iLQ,
    integral_const_mul, int_lin_lin hn, int_lin_quad hn, int_quad_quad hn]
  ring

/-- The non-constant features paired with a coefficient vector: linear form plus quadratic form. -/
lemma feat_rep (c : Mono n 2 → ℝ) (x : Fin n → ℝ) :
    ∑ q : JJ n, c q.1 * phiM x q.1 = linF (fun i => c (linQ i)) x + quadF (matOf c) x := by
  classical
  rw [sum_JJ (fun q => c q * phiM x q), sum_sym2 (fun z => c (quadQ z) * phiM x (quadQ z))]
  simp only [phiM_linQ, phiM_quadQ]
  unfold linF quadF
  congr 1
  have h : ∀ i j, matOf c i j * (x i * x j) = c (quadQ s(i, j)) * (x i * x j) / 2 +
      (if i = j then c (quadQ s(i, i)) * (x i * x i) / 2 else 0) := by
    intro i j
    unfold matOf
    split_ifs with hij
    · subst hij; ring
    · ring
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    ← Finset.sum_div]
  ring

lemma matOf_symm (c : Mono n 2 → ℝ) (i j : Fin n) : matOf c i j = matOf c j i := by
  unfold matOf
  rw [Sym2.eq_swap]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

lemma matOf_diag (c : Mono n 2 → ℝ) (i : Fin n) : matOf c i i = c (quadQ s(i, i)) := by
  unfold matOf; rw [if_pos rfl]; ring

lemma matOf_sq (c : Mono n 2 → ℝ) :
    ∑ i, ∑ j, matOf c i j * matOf c i j =
      (∑ i, ∑ j, c (quadQ s(i, j)) ^ 2) / 4 + 3 * (∑ i, c (quadQ s(i, i)) ^ 2) / 4 := by
  classical
  have h : ∀ i j, matOf c i j * matOf c i j = c (quadQ s(i, j)) ^ 2 / 4 +
      (if i = j then 3 * c (quadQ s(i, i)) ^ 2 / 4 else 0) := by
    intro i j
    unfold matOf
    split_ifs with hij
    · subst hij; ring
    · ring
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    ← Finset.sum_div, Finset.mul_sum]

/-- **The exact second moment** of a combination of the non-constant features. -/
theorem feat_sq_exact (hn : 1 ≤ n) (c : Mono n 2 → ℝ) :
    ∫ x, (∑ q : JJ n, c q.1 * phiM x q.1) ^ 2 ∂uniformSphere n =
      (∑ i, c (linQ i) ^ 2) / n +
        ((∑ i, c (quadQ s(i, i))) ^ 2 + (∑ i, ∑ j, c (quadQ s(i, j)) ^ 2) / 2 +
          3 * (∑ i, c (quadQ s(i, i)) ^ 2) / 2) / ((n : ℝ) * (n + 2)) := by
  simp_rw [feat_rep, int_sq hn]
  have h2 : ∑ i, ∑ j, matOf c i j * matOf c j i = ∑ i, ∑ j, matOf c i j * matOf c i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [matOf_symm c j i]
  rw [h2, matOf_sq]
  simp_rw [matOf_diag, ← sq]
  congr 1
  ring

/-- `‖c‖²` over the non-constant monomials. -/
lemma nsq_JJ (c : Mono n 2 → ℝ) :
    ∑ q : JJ n, c q.1 ^ 2 = ∑ i, c (linQ i) ^ 2 +
      (∑ i, ∑ j, c (quadQ s(i, j)) ^ 2 + ∑ i, c (quadQ s(i, i)) ^ 2) / 2 := by
  rw [sum_JJ (fun q => c q ^ 2), sum_sym2 (fun z => c (quadQ z) ^ 2)]

/-- **Feature operator bound with constant `1`.** -/
theorem featOp1 (n : ℕ) (hn : 1 ≤ n) : FeatOp n 1 := by
  classical
  intro c
  let c' : Mono n 2 → ℝ := fun q => if h : q ≠ default then c ⟨q, h⟩ else 0
  have hc : ∀ q : JJ n, c' q.1 = c q := fun q => by simp only [c']; rw [dif_pos q.2]
  have e1 : ∀ x : Fin n → ℝ, ∑ q, c q * pf x q = ∑ q : JJ n, c' q.1 * phiM x q.1 := by
    intro x; refine Finset.sum_congr rfl fun q _ => ?_
    rw [hc]; rfl
  have e2 : ∑ q, c q ^ 2 = ∑ q : JJ n, c' q.1 ^ 2 :=
    Finset.sum_congr rfl fun q _ => by rw [hc]
  simp_rw [e1]
  rw [e2, feat_sq_exact hn, nsq_JJ]
  set Sa := ∑ i, c' (linQ i) ^ 2
  set T := ∑ i, c' (quadQ s(i, i))
  set S := ∑ i, ∑ j, c' (quadQ s(i, j)) ^ 2
  set D := ∑ i, c' (quadQ s(i, i)) ^ 2
  have hT : T ^ 2 ≤ n * D := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => c' (quadQ s(i, i)))
    simpa using this
  have hDS : D ≤ S := by
    apply Finset.sum_le_sum; intro i _
    exact Finset.single_le_sum (f := fun j => c' (quadQ s(i, j)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have key : 1 / (n : ℝ) * (Sa + (S + D) / 2) -
      (Sa / n + (T ^ 2 + S / 2 + 3 * D / 2) / ((n : ℝ) * (n + 2))) =
      (((n : ℝ) + 2) * (S + D) / 2 - T ^ 2 - S / 2 - 3 * D / 2) / ((n : ℝ) * (n + 2)) := by
    field_simp
    ring
  have hnum : 0 ≤ ((n : ℝ) + 2) * (S + D) / 2 - T ^ 2 - S / 2 - 3 * D / 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1) (sub_nonneg.mpr hDS)]
  have := div_nonneg hnum (by positivity : (0 : ℝ) ≤ (n : ℝ) * (n + 2))
  linarith

/-- **The kernel formula**: `κ(x,y) = s + (s² + P)/2`. -/
theorem kap_formula' (x y : Fin n → ℝ) :
    kap x y = ∑ i, x i * y i + ((∑ i, x i * y i) ^ 2 + ∑ i, x i ^ 2 * y i ^ 2) / 2 := by
  unfold kap pf
  rw [sum_JJ (fun q => phiM x q * phiM y q), sum_sym2 (fun z => phiM x (quadQ z) * phiM y (quadQ z))]
  simp only [phiM_linQ, phiM_quadQ]
  congr 2
  congr 1
  · rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- The inner integral of `κ²`. -/
lemma inner_kap_sq (hn : 1 ≤ n) (x : Fin n → ℝ) :
    ∫ y, kap x y ^ 2 ∂uniformSphere n =
      (∑ i, x i ^ 2) / n + ((∑ i, x i ^ 2) ^ 2 + (∑ i, x i ^ 2) ^ 2 / 2 +
        3 * (∑ i, x i ^ 4) / 2) / ((n : ℝ) * (n + 2)) := by
  have h := feat_sq_exact hn (fun q => phiM x q)
  have e : ∀ y : Fin n → ℝ, kap x y = ∑ q : JJ n, phiM x q.1 * phiM y q.1 := fun y => rfl
  simp_rw [e, h, phiM_linQ, phiM_quadQ]
  have h1 : ∑ i, x i * x i = ∑ i, x i ^ 2 := Finset.sum_congr rfl fun i _ => (sq _).symm
  have h2 : ∑ i, ∑ j, (x i * x j) ^ 2 = (∑ i, x i ^ 2) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : ∑ i, (x i * x i) ^ 2 = ∑ i, x i ^ 4 := Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2, h3]

/-- **The exact value of `ss2 = E κ(x,y)²`.** -/
theorem ss2_exact (n : ℕ) (hn : 1 ≤ n) :
    ss2 n = 1 / (n : ℝ) + (3 * (n : ℝ) + 15) / (2 * (n : ℝ) * ((n : ℝ) + 2) ^ 2) := by
  classical
  have hP := BstLean.Part29.uniformSphere_isProbability n hn
  have hm := BstLean.Part29.uniformSphere_moments n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  unfold ss2
  simp_rw [inner_kap_sq hn]
  have hae : (fun x : Fin n → ℝ => (∑ i, x i ^ 2) / n + ((∑ i, x i ^ 2) ^ 2 +
      (∑ i, x i ^ 2) ^ 2 / 2 + 3 * (∑ i, x i ^ 4) / 2) / ((n : ℝ) * (n + 2)))
      =ᵐ[uniformSphere n] fun x => (1 / (n : ℝ) + 3 / 2 / ((n : ℝ) * (n + 2))) +
        3 / 2 / ((n : ℝ) * (n + 2)) * ∑ i, x i ^ 4 := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    rw [hx]; ring
  rw [integral_congr_ae hae]
  have hint : ∀ i : Fin n, Integrable (fun x : Fin n → ℝ => x i ^ 4) (uniformSphere n) := fun i =>
    sphere_cont_integrable' hn (by fun_prop)
  have h4 : ∀ i : Fin n, ∫ x, x i ^ 4 ∂uniformSphere n = 3 / ((n : ℝ) * (n + 2)) := by
    intro i
    have := hm.m4 i i i i
    simp only [and_self, ite_true] at this
    rw [show (fun x : Fin n → ℝ => x i ^ 4) = fun x => x i * x i * x i * x i from by
      funext x; ring, this]
    norm_num
  rw [integral_add (integrable_const _) ((integrable_finsetSum _ fun i _ => hint i).const_mul _),
    integral_const_mul, integral_finsetSum _ fun i _ => hint i]
  simp_rw [h4]
  simp only [integral_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    smul_eq_mul, probReal_univ]
  field_simp
  ring

end BstLean.Part78

#print axioms BstLean.Part78.featOp1
#print axioms BstLean.Part78.kap_formula'
#print axioms BstLean.Part78.feat_sq_exact
#print axioms BstLean.Part78.ss2_exact
