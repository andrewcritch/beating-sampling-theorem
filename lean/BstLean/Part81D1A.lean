import BstLean.Part81Defs
import BstLean.Part81Mean
import BstLean.Part81Bridge
import BstLean.Part81Core
import BstLean.Part81K1
import BstLean.Part29Index

/-!
# Part 81, map degree 1: the exact form of the error and its second moment

At `d = 1` the features are the coordinates, so `errG a H W` does not depend on `a`
(`errG1`), and the sphere error is `τ² · R` with `R = QW H W / n − (tr H / 𝒟) (|u|² + |W|²)`,
a centred quadratic form in the full Gaussian vector (`qform_comb`). Its second moment is
at most `2 ‖H‖² / n` (`secmom`).
-/

namespace BstLean.Part81.D1

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere qformι)
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part41 (Mono phiM)
open BstLean.Part78 (nsq frobH trH qfun aU zv Phi sph_int linF continuous_linF int_lin_lin)
open BstLean.Part81

variable {n : ℕ}

/-- Extension by zero of a row of `W` to all monomials. -/
noncomputable def eW (W : WIdx n 1 → ℝ) (i : Fin n) (q : Mono n 1) : ℝ :=
  if h : q ≠ default then W (⟨q, h⟩, i) else 0

lemma eW_JJ (W : WIdx n 1 → ℝ) (i : Fin n) (q : JJ n 1) : eW W i q.1 = W (q, i) := by
  simp [eW, q.2]

/-- The rows of `W` in the coordinate basis. -/
noncomputable def rW (W : WIdx n 1 → ℝ) (i k : Fin n) : ℝ := eW W i (K1.lin1 k)

lemma zv1 (W : WIdx n 1 → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    zv W (pf x) i = linF (rW W i) x := by
  unfold zv pf rW linF
  rw [← (funext fun k => by rw [K1.phi_lin1] :
    (fun k => eW W i (K1.lin1 k) * phiM x (K1.lin1 k)) = fun k => eW W i (K1.lin1 k) * x k),
    ← K1.sumJJ1 (fun p => eW W i p * phiM x p)]
  exact Finset.sum_congr rfl fun q _ => by rw [eW_JJ]

lemma sumJJ_W (W : WIdx n 1 → ℝ) (i j : Fin n) :
    ∑ q : JJ n 1, W (q, i) * W (q, j) = ∑ k, rW W i k * rW W j k := by
  unfold rW
  rw [← K1.sumJJ1 (fun p => eW W i p * eW W j p)]
  exact Finset.sum_congr rfl fun q _ => by rw [eW_JJ, eW_JJ]

/-- `Σ_{i,j} H_ij Σ_q W(q,i) W(q,j)`. -/
def QW (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n 1 → ℝ) : ℝ :=
  ∑ i, ∑ j, H i j * ∑ q : JJ n 1, W (q, i) * W (q, j)

/-- (i) At map degree 1 the mean of `F` over the sphere does not depend on `a`. -/
lemma int_FG1 (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n 1 → ℝ) :
    ∫ x, FG a H W x ∂uniformSphere n = QW H W / n := by
  have hF : ∀ x, FG a H W x = ∑ i, a i * linF (rW W i) x +
      ∑ i, ∑ j, H i j * (linF (rW W i) x * linF (rW W j) x) := by
    intro x
    unfold FG Phi
    simp only [zv1, mul_assoc]
  have i1 : ∀ i, Integrable (fun x => linF (rW W i) x) (uniformSphere n) :=
    fun i => sph_int hn (continuous_linF _)
  have i2 : ∀ i j, Integrable (fun x => linF (rW W i) x * linF (rW W j) x) (uniformSphere n) :=
    fun i j => sph_int hn ((continuous_linF _).mul (continuous_linF _))
  have e1 : ∫ x, ∑ i, a i * linF (rW W i) x ∂uniformSphere n = 0 := by
    rw [integral_finsetSum _ fun i _ => (i1 i).const_mul _]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul]
    have := K1.int_coord hn (rW W i)
    unfold linF
    rw [this, mul_zero]
  have e2 : ∫ x, ∑ i, ∑ j, H i j * (linF (rW W i) x * linF (rW W j) x) ∂uniformSphere n =
      QW H W / n := by
    rw [integral_finsetSum (f := fun i x => ∑ j, H i j * (linF (rW W i) x * linF (rW W j) x)) _
      fun i _ => integrable_finsetSum _ fun j _ => (i2 i j).const_mul _]
    unfold QW
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum (f := fun j x => H i j * (linF (rW W i) x * linF (rW W j) x)) _
      fun j _ => (i2 i j).const_mul _, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, int_lin_lin hn, sumJJ_W, mul_div_assoc]
  simp_rw [hF]
  rw [integral_add (f := fun x => ∑ i, a i * linF (rW W i) x)
    (g := fun x => ∑ i, ∑ j, H i j * (linF (rW W i) x * linF (rW W j) x))
    (integrable_finsetSum _ fun i _ => (i1 i).const_mul _)
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (i2 i j).const_mul _),
    e1, e2, zero_add]

/-- (i) At map degree 1 the Gaussian-model error does not depend on `a`. -/
lemma errG1 (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n 1 → ℝ) :
    errG a H W = QW H W / n - trH H := by
  unfold errG
  rw [int_FG1 hn, eD_one, one_mul]

lemma errG_indep (hn : 1 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n 1 → ℝ) :
    errG a H W = errG 0 H W := by
  rw [errG1 hn, errG1 hn]

/-! ## The matrix of the quadratic form -/

/-- The matrix of `(u, W) ↦ QW H W / n` in the split index. -/
noncomputable def BM (H : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ WIdx n 1) (Fin n ⊕ WIdx n 1) ℝ := fun a b =>
  Sum.elim (fun _ => 0) (fun p => Sum.elim (fun _ => 0)
    (fun p' => if p.1 = p'.1 then H p.2 p'.2 / n else 0) b) a

/-- The matrix of `Z ↦ QW H W / n` in the coefficient index. -/
noncomputable def AM (H : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (CoefIdxD n 1) (CoefIdxD n 1) ℝ := fun α α' =>
  BM H ((Br.splitEquiv n 1).symm α) ((Br.splitEquiv n 1).symm α')

lemma sumA (F : (Fin n ⊕ WIdx n 1) → (Fin n ⊕ WIdx n 1) → ℝ) :
    ∑ α, ∑ α', F ((Br.splitEquiv n 1).symm α) ((Br.splitEquiv n 1).symm α') = ∑ a, ∑ b, F a b := by
  rw [← Equiv.sum_comp (Br.splitEquiv n 1).symm (fun a => ∑ b, F a b)]
  refine Finset.sum_congr rfl fun α _ => ?_
  exact Equiv.sum_comp (Br.splitEquiv n 1).symm (F _)

lemma sum_diag (g : JJ n 1 → Fin n → JJ n 1 → Fin n → ℝ) :
    ∑ p : WIdx n 1, ∑ p' : WIdx n 1, (if p.1 = p'.1 then g p.1 p.2 p'.1 p'.2 else 0) =
      ∑ q, ∑ i, ∑ j, g q i q j := by
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single q]
  · simp
  · intro q' _ h
    simp [Ne.symm h]
  · simp

lemma sumJJ_const (c : ℝ) : ∑ _q : JJ n 1, c = n * c := by
  rw [K1.sumJJ1 (fun _ => c)]
  simp

lemma AM_symm (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) : (AM H).IsSymm := by
  apply Matrix.IsSymm.ext
  intro α α'
  unfold AM BM
  rcases (Br.splitEquiv n 1).symm α with a | p <;> rcases (Br.splitEquiv n 1).symm α' with b | p'
  · rfl
  · rfl
  · rfl
  · simp only [Sum.elim_inr]
    by_cases h : p.1 = p'.1
    · rw [if_pos h, if_pos h.symm, hH.apply]
    · rw [if_neg h, if_neg (Ne.symm h)]

lemma AM_trace (hn : 1 ≤ n) (H : Matrix (Fin n) (Fin n) ℝ) : ∑ k, AM H k k = trH H := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold AM
  rw [Equiv.sum_comp (Br.splitEquiv n 1).symm (fun a => BM H a a), Fintype.sum_sum_type]
  simp only [BM, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, zero_add, ite_true,
    Fintype.sum_prod_type]
  rw [sumJJ_const, ← Finset.sum_div]
  unfold trH
  field_simp

lemma AM_frob (hn : 1 ≤ n) (H : Matrix (Fin n) (Fin n) ℝ) :
    ∑ α, ∑ α', AM H α α' ^ 2 = frobH H / n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold AM
  rw [sumA (fun a b => BM H a b ^ 2)]
  have key : ∑ a, ∑ b, BM H a b ^ 2 = ∑ p : WIdx n 1, ∑ p' : WIdx n 1,
      (if p.1 = p'.1 then (H p.2 p'.2 / (n : ℝ)) ^ 2 else 0) := by
    simp [Fintype.sum_sum_type, BM, ite_pow]
  refine (key.trans (sum_diag (fun _ i _ j => (H i j / (n : ℝ)) ^ 2))).trans ?_
  rw [sumJJ_const]
  unfold frobH
  simp only [div_pow, ← Finset.sum_div]
  field_simp

lemma QW_alt (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n 1 → ℝ) :
    ∑ q : JJ n 1, ∑ i, ∑ j, H i j / (n : ℝ) * W (q, i) * W (q, j) = QW H W / n := by
  unfold QW
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- The centred quadratic form in the split coordinates. -/
lemma qform_comb (H : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (p : (Fin n → ℝ) × (WIdx n 1 → ℝ)) :
    qformι (AM H - c • (1 : Matrix (CoefIdxD n 1) (CoefIdxD n 1) ℝ)) (Br.combEquiv n 1 p) =
      QW H p.2 / n - c * (∑ i, p.1 i ^ 2 + ∑ β, p.2 β ^ 2) := by
  set Z := Br.combEquiv n 1 p with hZ
  have f3 : ∑ α, Z α ^ 2 = ∑ i, p.1 i ^ 2 + ∑ β, p.2 β ^ 2 := (Br.comb_facts p.1 p.2).2.2
  have h1 : ∀ α, ∑ α', (AM H - c • (1 : Matrix (CoefIdxD n 1) (CoefIdxD n 1) ℝ)) α α' * Z α * Z α'
      = ∑ α', AM H α α' * Z α * Z α' - c * Z α ^ 2 := by
    intro α
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single α]
    · simp; ring
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  unfold qformι
  simp only [h1, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, f3]
  congr 1
  have hZa : ∀ α, Z α = Sum.elim p.1 p.2 ((Br.splitEquiv n 1).symm α) :=
    fun α => Br.combEquiv_apply p α
  simp only [hZa, AM]
  rw [sumA (fun a b => BM H a b * Sum.elim p.1 p.2 a * Sum.elim p.1 p.2 b)]
  have key : ∑ a, ∑ b, BM H a b * Sum.elim p.1 p.2 a * Sum.elim p.1 p.2 b =
      ∑ q : WIdx n 1, ∑ q' : WIdx n 1, (if q.1 = q'.1 then
        H q.2 q'.2 / (n : ℝ) * p.2 (q.1, q.2) * p.2 (q'.1, q'.2) else 0) := by
    simp [Fintype.sum_sum_type, BM, ite_mul]
  exact (key.trans (sum_diag (fun a i b j => H i j / (n : ℝ) * p.2 (a, i) * p.2 (b, j)))).trans
    (QW_alt H p.2)

/-- `R(u, W) = QW H W / n − (tr H / 𝒟)(|u|² + |W|²)`. -/
noncomputable def Rf (H : Matrix (Fin n) (Fin n) ℝ) (p : (Fin n → ℝ) × (WIdx n 1 → ℝ)) : ℝ :=
  QW H p.2 / n - trH H / DD n 1 * (∑ i, p.1 i ^ 2 + ∑ β, p.2 β ^ 2)

/-- (iii) The second moment of `R` under the product Gaussian measure. -/
lemma secmom (hn : 1 ≤ n) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    Integrable (fun p => Rf H p ^ 2) ((stdGauss (Fin n)).prod (stdGauss (WIdx n 1))) ∧
    ∫ p, Rf H p ^ 2 ∂((stdGauss (Fin n)).prod (stdGauss (WIdx n 1))) ≤ 2 * frobH H / n := by
  have hcard : 0 < Fintype.card (CoefIdxD n 1) := by
    have hc := BstLean.Part36.DD_pos (d := 1) hn
    unfold DD at hc
    exact_mod_cast hc
  have hmp := Br.combEquiv_preserving (n := n) (d := 1)
  set f : (CoefIdxD n 1 → ℝ) → ℝ := fun Z =>
    qformι (AM H - ((∑ k, AM H k k) / Fintype.card (CoefIdxD n 1)) •
      (1 : Matrix (CoefIdxD n 1) (CoefIdxD n 1) ℝ)) Z ^ 2 with hf
  have hR : (fun p => Rf H p ^ 2) = f ∘ (Br.combEquiv n 1) := by
    funext p
    simp only [hf, Function.comp_apply, qform_comb, AM_trace hn]
    rfl
  have hi := BstLean.Part29.stdGauss_qform_sq_integrable
    (AM H - ((∑ k, AM H k k) / Fintype.card (CoefIdxD n 1)) • 1)
  have hb := BstLean.Part29.stdGauss_centred_sq_le hcard (AM H) (AM_symm H hH)
  rw [AM_frob hn] at hb
  rw [hR]
  refine ⟨(hmp.integrable_comp_emb (Br.combEquiv n 1).measurableEmbedding).mpr hi, ?_⟩
  have := hmp.integral_comp' f
  simp only [Function.comp_def]
  rw [this]
  refine hb.trans (le_of_eq ?_)
  ring

end BstLean.Part81.D1
