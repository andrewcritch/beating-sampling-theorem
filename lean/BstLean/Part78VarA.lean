import BstLean.Part78Defs
import BstLean.Part48Var

/-!
# Part 78, variance bound, file A: polynomial-valued functions of `x` with continuous coefficients

`PP d A`: `A x = Σ_s C (b_s x) * M_s` with finitely many continuous `b_s` and polynomials `M_s` of
total degree `≤ d`. Closed under sums and products; integrable against `uniformSphere n × stdGauss ι`;
the `x`-mean is again a polynomial (`PP.int`), with derivative the mean of the derivative.
-/

namespace BstLean.Part78

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss uniformSphere)

/-- Continuous functions are integrable under `uniformSphere n`. -/
lemma sphere_cont_integrable78 {n : ℕ} (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
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

set_option linter.unusedSectionVars false

variable {n : ℕ} {ι : Type} [Fintype ι]

/-- `A x = Σ_s C (b_s x) * M_s`, `b_s` continuous, `deg M_s ≤ d`. -/
def PP (d : ℕ) (A : (Fin n → ℝ) → MvPolynomial ι ℝ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (b : S → (Fin n → ℝ) → ℝ) (M : S → MvPolynomial ι ℝ),
    (∀ s, Continuous (b s)) ∧ (∀ s, (M s).totalDegree ≤ d) ∧ ∀ x, A x = ∑ s, C (b s x) * M s

namespace PP

lemma const {d : ℕ} (P : MvPolynomial ι ℝ) (hP : P.totalDegree ≤ d) :
    PP (n := n) d (fun _ => P) :=
  ⟨Unit, inferInstance, fun _ _ => 1, fun _ => P, fun _ => continuous_const, fun _ => hP,
    fun _ => by simp⟩

lemma coef {c : (Fin n → ℝ) → ℝ} (hc : Continuous c) :
    PP (ι := ι) 0 (fun x => C (c x)) :=
  ⟨Unit, inferInstance, fun _ => c, fun _ => 1, fun _ => hc, fun _ => by simp, fun _ => by simp⟩

lemma mono {d e : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ} (h : PP d A) (hde : d ≤ e) : PP e A := by
  obtain ⟨S, _, b, M, hb, hM, hA⟩ := h
  exact ⟨S, inferInstance, b, M, hb, fun s => (hM s).trans hde, hA⟩

lemma add {d : ℕ} {A B : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) (hB : PP d B) :
    PP d (fun x => A x + B x) := by
  obtain ⟨S, _, b, M, hb, hM, hA⟩ := hA
  obtain ⟨S', _, b', M', hb', hM', hB⟩ := hB
  refine ⟨S ⊕ S', inferInstance, Sum.elim b b', Sum.elim M M', ?_, ?_, ?_⟩
  · rintro (s | s) <;> simp [hb, hb']
  · rintro (s | s) <;> simp [hM, hM']
  · intro x; simp [Fintype.sum_sum_type, hA, hB]

lemma mul {d e : ℕ} {A B : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) (hB : PP e B) :
    PP (d + e) (fun x => A x * B x) := by
  obtain ⟨S, _, b, M, hb, hM, hA⟩ := hA
  obtain ⟨S', _, b', M', hb', hM', hB⟩ := hB
  refine ⟨S × S', inferInstance, fun s x => b s.1 x * b' s.2 x, fun s => M s.1 * M' s.2, ?_, ?_, ?_⟩
  · intro s; exact (hb s.1).mul (hb' s.2)
  · intro s; exact (totalDegree_mul _ _).trans (add_le_add (hM s.1) (hM' s.2))
  · intro x
    show A x * B x = _
    rw [hA, hB, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    simp only [C_mul]; ring

lemma neg {d : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) : PP d (fun x => - A x) := by
  have h := (const (n := n) (d := 0) (C (-1) : MvPolynomial ι ℝ) (by simp)).mul hA
  rw [zero_add] at h
  convert h using 2 with x
  simp

lemma sub {d : ℕ} {A B : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) (hB : PP d B) :
    PP d (fun x => A x - B x) := by
  have := hA.add hB.neg
  simpa only [sub_eq_add_neg] using this

lemma sum {d : ℕ} {κ : Type*} (s : Finset κ) {A : κ → (Fin n → ℝ) → MvPolynomial ι ℝ}
    (hA : ∀ k ∈ s, PP d (A k)) : PP d (fun x => ∑ k ∈ s, A k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (n := n) (d := d) (0 : MvPolynomial ι ℝ) (by simp)
  | insert a s ha ih =>
    have h1 := hA a (Finset.mem_insert_self a s)
    have h2 := ih fun k hk => hA k (Finset.mem_insert_of_mem hk)
    have := h1.add h2
    simpa only [Finset.sum_insert ha] using this

lemma cont {d : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) :
    Continuous (fun p : (Fin n → ℝ) × (ι → ℝ) => eval p.2 (A p.1)) := by
  obtain ⟨S, _, b, M, hb, hM, hA⟩ := hA
  simp only [hA, map_sum, map_mul, eval_C]
  refine continuous_finsetSum _ fun s _ => ?_
  exact ((hb s).comp continuous_fst).mul ((MvPolynomial.continuous_eval (M s)).comp continuous_snd)

lemma cont_x {d : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) (W : ι → ℝ) :
    Continuous (fun x : Fin n → ℝ => eval W (A x)) :=
  hA.cont.comp (Continuous.prodMk_left W)

lemma cont_W {d : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) (x : Fin n → ℝ) :
    Continuous (fun W : ι → ℝ => eval W (A x)) :=
  hA.cont.comp (Continuous.prodMk_right x)

lemma int_x {d : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) (hn : 1 ≤ n) (W : ι → ℝ) :
    Integrable (fun x : Fin n → ℝ => eval W (A x)) (uniformSphere n) :=
  sphere_cont_integrable78 hn (hA.cont_x W)

lemma int_prod {d : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) (hn : 1 ≤ n) :
    Integrable (fun p : (Fin n → ℝ) × (ι → ℝ) => eval p.2 (A p.1))
      ((uniformSphere n).prod (stdGauss ι)) := by
  obtain ⟨S, _, b, M, hb, hM, hA⟩ := hA
  simp only [hA, map_sum, map_mul, eval_C]
  refine integrable_finsetSum _ fun s _ => ?_
  exact (sphere_cont_integrable78 hn (hb s)).mul_prod (BstLean.Part48.gauss_poly_integrable (M s))

/-- The `x`-mean of a `PP` family is a polynomial; its derivative is the mean of the derivative. -/
lemma int {d : ℕ} {A : (Fin n → ℝ) → MvPolynomial ι ℝ} (hA : PP d A) (hn : 1 ≤ n) :
    ∃ Abar : MvPolynomial ι ℝ, Abar.totalDegree ≤ d ∧
      (∀ W, eval W Abar = ∫ x, eval W (A x) ∂uniformSphere n) ∧
      ∀ α W, eval W (pderiv α Abar) = ∫ x, eval W (pderiv α (A x)) ∂uniformSphere n := by
  obtain ⟨S, _, b, M, hb, hM, hA⟩ := hA
  refine ⟨∑ s, C (∫ x, b s x ∂uniformSphere n) * M s, ?_, ?_, ?_⟩
  · refine totalDegree_finsetSum_le fun s _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    simpa using hM s
  · intro W
    simp only [hA, map_sum, map_mul, eval_C]
    rw [integral_finsetSum _ fun s _ =>
      (sphere_cont_integrable78 hn (hb s)).mul_const _]
    exact Finset.sum_congr rfl fun s _ => (integral_mul_const _ _).symm
  · intro α W
    simp only [hA, map_sum, Derivation.leibniz, pderiv_C, smul_eq_mul, mul_zero, add_zero,
      map_mul, eval_C]
    rw [integral_finsetSum _ fun s _ =>
      (sphere_cont_integrable78 hn (hb s)).mul_const _]
    exact Finset.sum_congr rfl fun s _ => (integral_mul_const _ _).symm

end PP

end BstLean.Part78
