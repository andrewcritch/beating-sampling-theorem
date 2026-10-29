import BstLean.Part86Defs
import BstLean.Part84Poly
import BstLean.Part48Var

/-!
# Part 86, `Poly`: polynomial structure and regularity of the model functions

`polyFacts : Reg M d → PolyFacts M d`, and a small calculus (`PF`) of families of polynomials whose
coefficients are measurable and bounded functions of a parameter. Every model function
(`Fs`, `msl`, `Ysl`, `Bm`, `Vdn`, `Vm`, `Esl`) is such a family, in `W` (for a fixed scale) and in
the scale (for a fixed `W`); measurability, integrability and Fubini follow from `PF`.
-/

set_option linter.unusedSectionVars false

namespace BstLean.Part86

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss)
open BstLean.Part78 (zv)
open BstLean.Part84 (deg_aeval eval_aeval' totalDegree_finset_sum_le)

/-! ## §1 Measurable bounded functions -/

section mb

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Measurable and bounded. -/
def MB (c : α → ℝ) : Prop := Measurable c ∧ ∃ C : ℝ, ∀ a, |c a| ≤ C

lemma MB.const (r : ℝ) : MB (fun _ : α => r) := ⟨measurable_const, |r|, fun _ => le_rfl⟩

lemma MB.add {c c' : α → ℝ} (h : MB c) (h' : MB c') : MB (fun a => c a + c' a) := by
  obtain ⟨hm, C, hC⟩ := h
  obtain ⟨hm', C', hC'⟩ := h'
  exact ⟨hm.add hm', C + C', fun a => (abs_add_le _ _).trans (add_le_add (hC a) (hC' a))⟩

lemma MB.mul {c c' : α → ℝ} (h : MB c) (h' : MB c') : MB (fun a => c a * c' a) := by
  obtain ⟨hm, C, hC⟩ := h
  obtain ⟨hm', C', hC'⟩ := h'
  refine ⟨hm.mul hm', C * C', fun a => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC a) (hC' a) (abs_nonneg _) ((abs_nonneg _).trans (hC a))

lemma MB.neg {c : α → ℝ} (h : MB c) : MB (fun a => -c a) := by
  obtain ⟨hm, C, hC⟩ := h
  exact ⟨hm.neg, C, fun a => by rw [abs_neg]; exact hC a⟩

lemma MB.sub {c c' : α → ℝ} (h : MB c) (h' : MB c') : MB (fun a => c a - c' a) := by
  simpa [sub_eq_add_neg] using h.add h'.neg

lemma MB.sum {ι : Type*} (s : Finset ι) {c : ι → α → ℝ} (h : ∀ i ∈ s, MB (c i)) :
    MB (fun a => ∑ i ∈ s, c i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MB.const (α := α) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma MB.pow {c : α → ℝ} (h : MB c) (j : ℕ) : MB (fun a => c a ^ j) := by
  induction j with
  | zero => simpa using MB.const (α := α) 1
  | succ j ih => simpa [pow_succ] using ih.mul h

lemma MB.comp {c : α → ℝ} (h : MB c) {g : β → α} (hg : Measurable g) : MB (fun b => c (g b)) := by
  obtain ⟨hm, C, hC⟩ := h
  exact ⟨hm.comp hg, C, fun b => hC (g b)⟩

lemma MB.integrable {c : α → ℝ} (h : MB c) (μ : Measure α) [IsFiniteMeasure μ] :
    Integrable c μ := by
  obtain ⟨hm, C, hC⟩ := h
  exact Integrable.mono' (integrable_const C) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a => by simpa [Real.norm_eq_abs] using hC a))

lemma MB.integral_right {c : α × β → ℝ} (h : MB c) (μ : Measure β) [IsProbabilityMeasure μ] :
    MB (fun a => ∫ b, c (a, b) ∂μ) := by
  obtain ⟨hm, C, hC⟩ := h
  refine ⟨(hm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable, C, fun a => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun b => c (a, b)) (C := C)
    (Filter.Eventually.of_forall (fun b => by simpa [Real.norm_eq_abs] using hC (a, b)))
  simpa [Real.norm_eq_abs] using this

end mb

/-! ## §2 Families of polynomials with measurable bounded coefficients -/

section pf

variable {τ : Type} [Fintype τ] {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- `f a` is a polynomial of degree `≤ K` in `W : τ → ℝ` whose coefficients are measurable and
bounded functions of the parameter `a`. -/
def PF (K : ℕ) (f : α → (τ → ℝ) → ℝ) : Prop :=
  ∃ Q : α → MvPolynomial τ ℝ, (∀ a, (Q a).totalDegree ≤ K) ∧
    (∀ m, MB fun a => (Q a).coeff m) ∧ ∀ a W, eval W (Q a) = f a W

lemma expFin (τ : Type) [Fintype τ] (K : ℕ) : {m : τ →₀ ℕ | (m.sum fun _ e => e) ≤ K}.Finite := by
  have := Finsupp.finite_of_degree_le (σ := τ) K
  refine this.subset (fun m hm => ?_)
  simpa [Finsupp.degree_apply, Finsupp.sum] using hm

/-- The exponents of degree `≤ K`. -/
noncomputable def expSet (τ : Type) [Fintype τ] (K : ℕ) : Finset (τ →₀ ℕ) := (expFin τ K).toFinset

/-- The value of a monomial. -/
def monv (m : τ →₀ ℕ) (W : τ → ℝ) : ℝ := ∏ i ∈ m.support, W i ^ m i

lemma measurable_monv (m : τ →₀ ℕ) : Measurable (monv m) := by
  unfold monv
  exact Finset.measurable_prod _ (fun i _ => (measurable_pi_apply i).pow_const _)

lemma eval_expand {K : ℕ} (Q : MvPolynomial τ ℝ) (hQ : Q.totalDegree ≤ K) (W : τ → ℝ) :
    eval W Q = ∑ m ∈ expSet τ K, Q.coeff m * monv m W := by
  rw [eval_eq]
  refine Finset.sum_subset (fun m hm => ?_) (fun m _ hm => ?_)
  · unfold expSet
    rw [Set.Finite.mem_toFinset]
    exact (le_totalDegree hm).trans hQ
  · rw [notMem_support_iff.mp hm, zero_mul]

lemma integrable_monv (m : τ →₀ ℕ) : Integrable (monv m) (stdGauss τ) := by
  have h := BstLean.Part48.gauss_poly_integrable (monomial m (1 : ℝ))
  have e : (fun z : τ → ℝ => eval z (monomial m (1 : ℝ))) = monv m := by
    funext z
    rw [eval_monomial, one_mul]
    rfl
  rwa [e] at h

namespace PF

variable {K K' : ℕ} {f f' : α → (τ → ℝ) → ℝ}

lemma mono (h : PF K f) (hK : K ≤ K') : PF K' f := by
  obtain ⟨Q, hd, hm, he⟩ := h
  exact ⟨Q, fun a => (hd a).trans hK, hm, he⟩

lemma add (h : PF K f) (h' : PF K f') : PF K (fun a W => f a W + f' a W) := by
  obtain ⟨Q, hd, hm, he⟩ := h
  obtain ⟨Q', hd', hm', he'⟩ := h'
  refine ⟨fun a => Q a + Q' a, fun a => (totalDegree_add _ _).trans (max_le (hd a) (hd' a)),
    fun m => ?_, fun a W => by rw [map_add, he, he']⟩
  simp only [AddMonoidAlgebra.coeff_add]
  exact (hm m).add (hm' m)

lemma sub (h : PF K f) (h' : PF K f') : PF K (fun a W => f a W - f' a W) := by
  obtain ⟨Q, hd, hm, he⟩ := h
  obtain ⟨Q', hd', hm', he'⟩ := h'
  refine ⟨fun a => Q a - Q' a, fun a => (totalDegree_sub _ _).trans (max_le (hd a) (hd' a)),
    fun m => ?_, fun a W => by rw [map_sub, he, he']⟩
  simp only [coeff_sub]
  exact (hm m).sub (hm' m)

lemma mul (h : PF K f) (h' : PF K' f') : PF (K + K') (fun a W => f a W * f' a W) := by
  classical
  obtain ⟨Q, hd, hm, he⟩ := h
  obtain ⟨Q', hd', hm', he'⟩ := h'
  refine ⟨fun a => Q a * Q' a,
    fun a => (totalDegree_mul _ _).trans (add_le_add (hd a) (hd' a)),
    fun m => ?_, fun a W => by rw [map_mul, he, he']⟩
  simp only [coeff_mul]
  exact MB.sum _ (fun x _ => (hm x.1).mul (hm' x.2))

lemma const {c : α → ℝ} (hc : MB c) : PF (τ := τ) 0 (fun a _ => c a) := by
  classical
  refine ⟨fun a => C (c a), fun a => by rw [totalDegree_C], fun m => ?_, fun a W => by simp⟩
  simp only [coeff_C]
  by_cases h0 : (0 : τ →₀ ℕ) = m
  · simpa [h0] using hc
  · simpa [h0] using MB.const (α := α) 0

lemma pow (h : PF K f) (j : ℕ) : PF (j * K) (fun a W => f a W ^ j) := by
  induction j with
  | zero => simpa using const (τ := τ) (MB.const (α := α) 1)
  | succ j ih =>
    have := ih.mul h
    have e : (j + 1) * K = j * K + K := by ring
    rw [e]
    simpa [pow_succ] using this

lemma comp (h : PF K f) {g : β → α} (hg : Measurable g) : PF K (fun b W => f (g b) W) := by
  obtain ⟨Q, hd, hm, he⟩ := h
  exact ⟨fun b => Q (g b), fun b => hd _, fun m => (hm m).comp hg, fun b W => he _ W⟩

/-- The expansion over the finite set of exponents of degree `≤ K`. -/
lemma expansion (h : PF K f) : ∃ c : (τ →₀ ℕ) → α → ℝ, (∀ m, MB (c m)) ∧
    ∀ a W, f a W = ∑ m ∈ expSet τ K, c m a * monv m W := by
  obtain ⟨Q, hd, hm, he⟩ := h
  exact ⟨fun m a => (Q a).coeff m, hm, fun a W => by rw [← he, eval_expand _ (hd a)]⟩

/-- Integration over a part of the parameter. -/
lemma integral {f : α × β → (τ → ℝ) → ℝ} (h : PF K f) (μ : Measure β) [IsProbabilityMeasure μ] :
    PF K (fun a W => ∫ b, f (a, b) W ∂μ) := by
  classical
  obtain ⟨c, hc, he⟩ := h.expansion
  refine ⟨fun a => ∑ m ∈ expSet τ K, monomial m (∫ b, c m (a, b) ∂μ), fun a => ?_, fun m => ?_,
    fun a W => ?_⟩
  · refine totalDegree_finset_sum_le (fun m hm => ?_)
    refine (totalDegree_monomial_le _ _).trans ?_
    unfold expSet at hm
    exact (expFin τ K).mem_toFinset.mp hm
  · simp only [coeff_sum, coeff_monomial]
    exact MB.sum _ (fun m' _ => by
      by_cases h0 : m' = m
      · simpa [h0] using (hc m).integral_right μ
      · simpa [h0] using MB.const (α := α) 0)
  · rw [map_sum]
    simp only [he]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [eval_monomial, integral_mul_const]
      rfl
    · intro m _
      exact (((hc m).comp (measurable_prodMk_left (x := a))).integrable μ).mul_const _

/-- Joint measurability. -/
lemma measurable (h : PF K f) : Measurable (fun z : α × (τ → ℝ) => f z.1 z.2) := by
  obtain ⟨c, hc, he⟩ := h.expansion
  simp only [he]
  exact Finset.measurable_sum _ (fun m _ =>
    ((hc m).1.comp measurable_fst).mul ((measurable_monv m).comp measurable_snd))

lemma measurable_left (h : PF K f) (W : τ → ℝ) : Measurable (fun a => f a W) :=
  h.measurable.comp (measurable_prodMk_right (y := W))

lemma measurable_right (h : PF K f) (a : α) : Measurable (f a) :=
  h.measurable.comp (measurable_prodMk_left (x := a))

/-- For a fixed `W`, the function of the parameter is measurable and bounded. -/
lemma mb (h : PF K f) (W : τ → ℝ) : MB (fun a => f a W) := by
  obtain ⟨c, hc, he⟩ := h.expansion
  simp only [he]
  exact MB.sum _ (fun m _ => (hc m).mul (MB.const _))

/-- A Gaussian-integrable majorant that does not depend on the parameter. -/
lemma dom (h : PF K f) : ∃ G : (τ → ℝ) → ℝ, (∀ W, 0 ≤ G W) ∧ Integrable G (stdGauss τ) ∧
    ∀ a W, |f a W| ≤ G W := by
  obtain ⟨c, hc, he⟩ := h.expansion
  choose B hB using fun m => (hc m).2
  refine ⟨fun W => ∑ m ∈ expSet τ K, |B m| * |monv m W|,
    fun W => Finset.sum_nonneg (fun m _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)), ?_, ?_⟩
  · exact integrable_finsetSum _ (fun m _ => (integrable_monv m).abs.const_mul _)
  · intro a W
    rw [he]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ((hB m a).trans (le_abs_self _)) (abs_nonneg _)

/-- Integrability in `W` under the standard Gaussian. -/
lemma integrable (h : PF K f) (a : α) : Integrable (f a) (stdGauss τ) := by
  obtain ⟨G, -, hG, hb⟩ := h.dom
  exact Integrable.mono' hG (h.measurable_right a).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun W => by simpa [Real.norm_eq_abs] using hb a W))

/-- Integrability on the product with a finite measure on the parameter. -/
lemma integrable_prod (h : PF K f) (μ : Measure α) [IsFiniteMeasure μ] :
    Integrable (fun z : α × (τ → ℝ) => f z.1 z.2) (μ.prod (stdGauss τ)) := by
  obtain ⟨G, -, hG, hb⟩ := h.dom
  exact Integrable.mono' (hG.comp_snd μ) h.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by simpa [Real.norm_eq_abs] using hb z.1 z.2))

/-- Fubini: the Gaussian integral and the integral over the parameter commute. -/
lemma fubini (h : PF K f) (μ : Measure α) [IsFiniteMeasure μ] :
    ∫ W, ∫ a, f a W ∂μ ∂stdGauss τ = ∫ a, ∫ W, f a W ∂stdGauss τ ∂μ :=
  (integral_integral_swap (h.integrable_prod μ)).symm

/-- The Gaussian mean is a measurable bounded function of the parameter. -/
lemma mb_integral (h : PF K f) : MB (fun a => ∫ W, f a W ∂stdGauss τ) := by
  obtain ⟨G, hG0, hG, hb⟩ := h.dom
  refine ⟨(h.measurable.stronglyMeasurable.integral_prod_right' (ν := stdGauss τ)).measurable,
    ∫ W, G W ∂stdGauss τ, fun a => ?_⟩
  refine (abs_integral_le_integral_abs).trans ?_
  exact integral_mono (h.integrable a).abs hG (fun W => hb a W)

/-- For each parameter there is a polynomial of degree `≤ K`. -/
lemma exists_poly (h : PF K f) (a : α) : ∃ Q : MvPolynomial τ ℝ, Q.totalDegree ≤ K ∧
    ∀ W, eval W Q = f a W := by
  obtain ⟨Q, hd, -, he⟩ := h
  exact ⟨Q a, hd a, he a⟩

end PF

end pf

/-! ## §3 Substitution -/

section subst

variable {σ τ : Type*} {α : Type*} [MeasurableSpace α]

/-- Substitution of polynomials of degree `≤ d` multiplies the degree by at most `d`. -/
lemma deg_aeval_mul (L : σ → MvPolynomial τ ℝ) (d : ℕ) (hL : ∀ i, (L i).totalDegree ≤ d)
    (P : MvPolynomial σ ℝ) : (aeval L P).totalDegree ≤ d * P.totalDegree := by
  rw [aeval_def, eval₂_eq]
  refine totalDegree_finset_sum_le (fun m hm => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ m.support, (L i ^ m i).totalDegree ≤ ∑ i ∈ m.support, m i * d :=
        Finset.sum_le_sum (fun i _ => (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hL i)))
    _ = (m.sum fun _ e => e) * d := by unfold Finsupp.sum; rw [Finset.sum_mul]
    _ ≤ P.totalDegree * d := Nat.mul_le_mul_right _ (le_totalDegree hm)
    _ = d * P.totalDegree := mul_comm _ _

/-- A family of polynomials whose coefficients are measurable and bounded. -/
def MBP (p : α → MvPolynomial τ ℝ) : Prop := ∀ m, MB fun a => (p a).coeff m

lemma MBP.C {c : α → ℝ} (hc : MB c) : MBP (τ := τ) (fun a => MvPolynomial.C (c a)) := by
  classical
  intro m
  simp only [coeff_C]
  by_cases h0 : (0 : τ →₀ ℕ) = m
  · simpa [h0] using hc
  · simpa [h0] using MB.const (α := α) 0

lemma MBP.constp (q : MvPolynomial τ ℝ) : MBP (fun _ : α => q) := fun m => MB.const _

lemma MBP.mul {p p' : α → MvPolynomial τ ℝ} (h : MBP p) (h' : MBP p') :
    MBP (fun a => p a * p' a) := by
  classical
  intro m
  simp only [coeff_mul]
  exact MB.sum _ (fun x _ => (h x.1).mul (h' x.2))

lemma MBP.sum {ι : Type*} (s : Finset ι) {p : ι → α → MvPolynomial τ ℝ} (h : ∀ i ∈ s, MBP (p i)) :
    MBP (fun a => ∑ i ∈ s, p i a) := by
  intro m
  simp only [coeff_sum]
  exact MB.sum _ (fun i hi => h i hi m)

/-- The coefficients of a substitution are measurable and bounded in the parameter. -/
lemma MBP.aeval (L : α → σ → MvPolynomial τ ℝ) (hL : ∀ i, MBP fun a => L a i)
    (P : MvPolynomial σ ℝ) : MBP fun a => MvPolynomial.aeval (L a) P := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [aeval_C, algebraMap_eq]
    exact MBP.constp _
  | add p q hp hq =>
    intro m
    simp only [map_add, AddMonoidAlgebra.coeff_add]
    exact (hp m).add (hq m)
  | mul_X p i hp =>
    simp only [map_mul, aeval_X]
    exact hp.mul (hL i)

end subst

/-- A substitution of linear forms with measurable bounded coefficients is a `PF` family. -/
lemma PF.of_aeval {σ : Type*} {τ : Type} [Fintype τ] {α : Type*} [MeasurableSpace α] {K : ℕ}
    (L : α → σ → MvPolynomial τ ℝ) (hLd : ∀ a i, (L a i).totalDegree ≤ 1)
    (hL : ∀ i, MBP fun a => L a i) (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ K) :
    PF K (fun a W => eval W (aeval (L a) P)) :=
  ⟨fun a => aeval (L a) P, fun a => (deg_aeval _ (hLd a) P).trans hP, MBP.aeval L hL P,
    fun _ _ => rfl⟩

/-- A `PF` family in one variable gives polynomials in `Polynomial ℝ`. -/
lemma PF.exists_poly1 {α : Type*} [MeasurableSpace α] {K : ℕ} {f : α → (Unit → ℝ) → ℝ}
    (h : PF K f) (a : α) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ K ∧ ∀ lam : ℝ, q.eval lam = f a (fun _ => lam) := by
  obtain ⟨Q, hd, -, he⟩ := h
  refine ⟨∑ m ∈ (Q a).support, Polynomial.C ((Q a).coeff m) * Polynomial.X ^ (m ()), ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun m hm => ?_)
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    refine le_trans ?_ ((le_totalDegree hm).trans (hd a))
    unfold Finsupp.sum
    by_cases h0 : m () = 0
    · rw [h0]; exact Nat.zero_le _
    · exact Finset.single_le_sum (f := fun i => m i) (fun _ _ => Nat.zero_le _)
        (Finsupp.mem_support_iff.mpr h0)
  · intro lam
    rw [← he, eval_eq, Polynomial.eval_finsetSum]
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

/-! ## §4 Slice quantities of a `PF` family on `S × G` -/

section slice

variable {S G : Type} [MeasurableSpace S] [MeasurableSpace G] {τ : Type} [Fintype τ]

lemma mb_sq_sub {α : Type*} [MeasurableSpace α] {c : α → ℝ} (h : MB c) (μ : Measure α)
    [IsProbabilityMeasure μ] (r : ℝ) :
    ∫ a, (c a - r) ^ 2 ∂μ = ∫ a, c a * c a ∂μ - 2 * r * ∫ a, c a ∂μ + r ^ 2 := by
  have e : ∀ a, (c a - r) ^ 2 = c a * c a - 2 * r * c a + r ^ 2 := fun a => by ring
  simp only [e]
  have h2 := (h.mul h).integrable μ
  have h1 := (h.integrable μ).const_mul (2 * r)
  have e1 := integral_add (h2.sub h1) (integrable_const (μ := μ) (r ^ 2))
  have e2 := integral_sub h2 h1
  have e3 := integral_const_mul (μ := μ) (2 * r) c
  simp only [Pi.sub_apply] at e1
  rw [e1, e2, e3, integral_const]
  simp

/-- The slice mean. -/
noncomputable def gm (γ : Measure G) (F : S × G → (τ → ℝ) → ℝ) (p : S) (w : τ → ℝ) : ℝ :=
  ∫ g, F (p, g) w ∂γ

/-- The total mean. -/
noncomputable def gB (π : Measure S) (γ : Measure G) (F : S × G → (τ → ℝ) → ℝ) (w : τ → ℝ) : ℝ :=
  ∫ p, gm γ F p w ∂π

/-- The slice variance. -/
noncomputable def gY (γ : Measure G) (F : S × G → (τ → ℝ) → ℝ) (p : S) (w : τ → ℝ) : ℝ :=
  ∫ g, (F (p, g) w - gm γ F p w) ^ 2 ∂γ

/-- The within-slice variance. -/
noncomputable def gVd (π : Measure S) (γ : Measure G) (F : S × G → (τ → ℝ) → ℝ) (w : τ → ℝ) : ℝ :=
  ∫ p, gY γ F p w ∂π

/-- The total variance. -/
noncomputable def gV (π : Measure S) (γ : Measure G) (F : S × G → (τ → ℝ) → ℝ) (w : τ → ℝ) : ℝ :=
  ∫ p, ∫ g, (F (p, g) w - gB π γ F w) ^ 2 ∂γ ∂π

variable (π : Measure S) (γ : Measure G) [IsProbabilityMeasure π] [IsProbabilityMeasure γ]
  {K : ℕ} {F : S × G → (τ → ℝ) → ℝ}

/-- Integration of a family on `S` over the whole parameter. -/
lemma PF.unit {f : S → (τ → ℝ) → ℝ} (h : PF K f) :
    PF K (fun (_ : Unit) w => ∫ p, f p w ∂π) :=
  (h.comp (measurable_snd : Measurable (Prod.snd : Unit × S → S))).integral π

lemma pf_gm (hF : PF K F) : PF K (fun p w => gm γ F p w) := hF.integral γ

lemma pf_gB (hF : PF K F) : PF K (fun (_ : Unit) w => gB π γ F w) := (pf_gm γ hF).unit π

lemma gY_eq (hF : PF K F) (p : S) (w : τ → ℝ) :
    gY γ F p w = gm γ (fun a w => F a w * F a w) p w - gm γ F p w ^ 2 := by
  have h := (hF.mb w).comp (measurable_prodMk_left (x := p) : Measurable fun g : G => (p, g))
  unfold gY
  rw [mb_sq_sub h γ]
  unfold gm
  ring

lemma pf_gY (hF : PF K F) : PF (2 * K) (fun p w => gY γ F p w) := by
  have h := (pf_gm γ (hF.mul hF)).sub ((pf_gm γ hF).mul (pf_gm γ hF))
  rw [two_mul]
  have e : (fun p w => gY γ F p w) = fun p w =>
      gm γ (fun a w => F a w * F a w) p w - gm γ F p w * gm γ F p w := by
    funext p w
    rw [gY_eq γ hF, sq]
  rw [e]
  exact h

lemma pf_gVd (hF : PF K F) : PF (2 * K) (fun (_ : Unit) w => gVd π γ F w) := (pf_gY γ hF).unit π

lemma gV_eq (hF : PF K F) (w : τ → ℝ) :
    gV π γ F w = gB π γ (fun a w => F a w * F a w) w - gB π γ F w ^ 2 := by
  have hin : ∀ p, ∫ g, (F (p, g) w - gB π γ F w) ^ 2 ∂γ =
      gm γ (fun a w => F a w * F a w) p w - 2 * gB π γ F w * gm γ F p w + gB π γ F w ^ 2 := by
    intro p
    have h := (hF.mb w).comp (measurable_prodMk_left (x := p) : Measurable fun g : G => (p, g))
    rw [mb_sq_sub h γ]
    rfl
  unfold gV
  simp only [hin]
  have h2 := ((pf_gm γ (hF.mul hF)).mb w).integrable π
  have h1 := (((pf_gm γ hF).mb w).integrable π).const_mul (2 * gB π γ F w)
  have e1 := integral_add (h2.sub h1) (integrable_const (μ := π) (gB π γ F w ^ 2))
  have e2 := integral_sub h2 h1
  have e3 := integral_const_mul (μ := π) (2 * gB π γ F w) (fun p => gm γ F p w)
  simp only [Pi.sub_apply] at e1
  rw [e1, e2, e3, integral_const]
  simp only [gB]
  simp
  ring

lemma pf_gV (hF : PF K F) : PF (2 * K) (fun (_ : Unit) w => gV π γ F w) := by
  have h := (pf_gB π γ (hF.mul hF)).sub ((pf_gB π γ hF).mul (pf_gB π γ hF))
  rw [two_mul]
  have e : (fun (_ : Unit) w => gV π γ F w) = fun (_ : Unit) w =>
      gB π γ (fun a w => F a w * F a w) w - gB π γ F w * gB π γ F w := by
    funext _ w
    rw [gV_eq π γ hF, sq]
  rw [e]
  exact h

/-- The law of total variance. -/
lemma gV_decomp (hF : PF K F) (w : τ → ℝ) :
    gV π γ F w = gVd π γ F w + ∫ p, (gm γ F p w - gB π γ F w) ^ 2 ∂π := by
  have hm := (pf_gm γ hF).mb w
  have hm2 := (pf_gm γ (hF.mul hF)).mb w
  rw [gV_eq π γ hF, mb_sq_sub hm π]
  unfold gVd
  simp only [gY_eq γ hF, sq]
  rw [integral_sub (hm2.integrable π) ((hm.mul hm).integrable π)]
  simp only [gB]
  ring

end slice

/-! ## §5 The model -/

section model

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

/-! ### Scaling -/

theorem Fm_smul (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam t : ℝ)
    (W : J × Fin n → ℝ) (x : Fin n → ℝ) : Fm M P lam (t • W) x = Fm M P (lam * t) W x := by
  unfold Fm
  have h : (fun i => lam * zv (t • W) (M.ps x) i) = fun i => lam * t * zv W (M.ps x) i := by
    funext i
    simp only [zv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [h]

theorem Fs_smul (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam t : ℝ)
    (W : J × Fin n → ℝ) (p : S) (g : G) : Fs M P lam (t • W) p g = Fs M P (lam * t) W p g :=
  Fm_smul M P lam t W _

theorem msl_smul (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam t : ℝ)
    (W : J × Fin n → ℝ) (p : S) : msl M P lam (t • W) p = msl M P (lam * t) W p := by
  unfold msl; simp only [Fs_smul]

theorem Ysl_smul (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam t : ℝ)
    (W : J × Fin n → ℝ) (p : S) : Ysl M P lam (t • W) p = Ysl M P (lam * t) W p := by
  unfold Ysl; simp only [Fs_smul, msl_smul]

theorem Bm_smul (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam t : ℝ)
    (W : J × Fin n → ℝ) : Bm M P lam (t • W) = Bm M P (lam * t) W := by
  unfold Bm; simp only [msl_smul]

theorem Vm_smul (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam t : ℝ)
    (W : J × Fin n → ℝ) : Vm M P lam (t • W) = Vm M P (lam * t) W := by
  unfold Vm; simp only [Fs_smul, Bm_smul]

theorem Vdn_smul (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam t : ℝ)
    (W : J × Fin n → ℝ) : Vdn M P lam (t • W) = Vdn M P (lam * t) W := by
  unfold Vdn; simp only [Ysl_smul]

/-! ### The features on the unit ball -/

lemma prod_abs_le_one {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, |f i| ≤ 1) :
    ∏ i ∈ s, |f i| ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact mul_le_one₀ (h i (Finset.mem_insert_self _ _))
      (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma ball_bound (Q : MvPolynomial (Fin n) ℝ) :
    ∃ C : ℝ, ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 ≤ 1 → |eval x Q| ≤ C := by
  refine ⟨∑ m ∈ Q.support, |Q.coeff m|, fun x hx => ?_⟩
  have hx1 : ∀ i, |x i| ≤ 1 := by
    intro i
    have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
      Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    exact (sq_le_one_iff_abs_le_one _).mp (h1.trans hx)
  rw [eval_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
  rw [abs_mul, Finset.abs_prod]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  refine prod_abs_le_one _ _ (fun i _ => ?_)
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (hx1 i)

lemma mb_feat (M : Mod n I J S G) {d : ℕ} (hR : Reg M d) (Q : MvPolynomial (Fin n) ℝ) :
    MB (fun a : S × G => eval (M.X a) Q) := by
  obtain ⟨C, hC⟩ := ball_bound Q
  exact ⟨(MvPolynomial.continuous_eval Q).measurable.comp hR.2.2.1, C,
    fun a => hC _ (hR.2.2.2.1 a)⟩

/-! ### The three substitutions -/

/-- The linear forms in `W`: `b_j(x)` and `lam · (W ψ(x))_i`. -/
noncomputable def LWm (M : Mod n I J S G) (lam : ℝ) (x : Fin n → ℝ) :
    I ⊕ Fin n → MvPolynomial (J × Fin n) ℝ :=
  Sum.elim (fun j => C (M.b x j)) (fun i => C lam * ∑ q : J, C (M.ps x q) * X (q, i))

lemma LWm_deg (M : Mod n I J S G) (lam : ℝ) (x : Fin n → ℝ) (s : I ⊕ Fin n) :
    (LWm M lam x s).totalDegree ≤ 1 := by
  cases s with
  | inl j => simp [LWm]
  | inr i =>
    simp only [LWm, Sum.elim_inr]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine totalDegree_finset_sum_le (fun q _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_X _).le

lemma LWm_eval (M : Mod n I J S G) (lam : ℝ) (x : Fin n → ℝ) (P : MvPolynomial (I ⊕ Fin n) ℝ)
    (W : J × Fin n → ℝ) : eval W (aeval (LWm M lam x) P) = Fm M P lam W x := by
  rw [eval_aeval']
  unfold Fm
  have h : (fun s => eval W (LWm M lam x s)) = Sum.elim (M.b x) (fun i => lam * zv W (M.ps x) i) := by
    funext s
    cases s with
    | inl j => simp [LWm]
    | inr i => simp [LWm, zv, mul_comm]
  rw [h]

lemma LWm_mbp (M : Mod n I J S G) {d : ℕ} (hR : Reg M d) (lam : ℝ) (s : I ⊕ Fin n) :
    MBP fun a : S × G => LWm M lam (M.X a) s := by
  cases s with
  | inl j =>
    simp only [LWm, Sum.elim_inl]
    exact MBP.C (mb_feat M hR _)
  | inr i =>
    simp only [LWm, Sum.elim_inr]
    exact (MBP.constp _).mul (MBP.sum _ (fun q _ => (MBP.C (mb_feat M hR _)).mul (MBP.constp _)))

/-- The linear forms in the scale: `b_j(x)` and `lam · (W ψ(x))_i`, in one variable. -/
noncomputable def LRm (M : Mod n I J S G) (W : J × Fin n → ℝ) (x : Fin n → ℝ) :
    I ⊕ Fin n → MvPolynomial Unit ℝ :=
  Sum.elim (fun j => C (M.b x j)) (fun i => C (zv W (M.ps x) i) * X ())

lemma LRm_deg (M : Mod n I J S G) (W : J × Fin n → ℝ) (x : Fin n → ℝ) (s : I ⊕ Fin n) :
    (LRm M W x s).totalDegree ≤ 1 := by
  cases s with
  | inl j => simp [LRm]
  | inr i =>
    simp only [LRm, Sum.elim_inr]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_X _).le

lemma LRm_eval (M : Mod n I J S G) (W : J × Fin n → ℝ) (x : Fin n → ℝ)
    (P : MvPolynomial (I ⊕ Fin n) ℝ) (l : Unit → ℝ) :
    eval l (aeval (LRm M W x) P) = Fm M P (l ()) W x := by
  rw [eval_aeval']
  unfold Fm
  have h : (fun s => eval l (LRm M W x s)) = Sum.elim (M.b x) (fun i => l () * zv W (M.ps x) i) := by
    funext s
    cases s with
    | inl j => simp [LRm]
    | inr i => simp [LRm, mul_comm]
  rw [h]

lemma LRm_mbp (M : Mod n I J S G) {d : ℕ} (hR : Reg M d) (W : J × Fin n → ℝ) (s : I ⊕ Fin n) :
    MBP fun a : S × G => LRm M W (M.X a) s := by
  cases s with
  | inl j =>
    simp only [LRm, Sum.elim_inl]
    exact MBP.C (mb_feat M hR _)
  | inr i =>
    simp only [LRm, Sum.elim_inr]
    refine (MBP.C ?_).mul (MBP.constp _)
    unfold zv
    exact MB.sum _ (fun q _ => (MB.const _).mul (mb_feat M hR _))

/-- The polynomials in `x`: `b_j` and `lam · Σ_q W(q,i) ψ_q`. -/
noncomputable def LXm (M : Mod n I J S G) (lam : ℝ) (W : J × Fin n → ℝ) :
    I ⊕ Fin n → MvPolynomial (Fin n) ℝ :=
  Sum.elim M.bP (fun i => C lam * ∑ q : J, C (W (q, i)) * M.psP q)

lemma LXm_deg (M : Mod n I J S G) {d : ℕ} (hR : Reg M d) (lam : ℝ) (W : J × Fin n → ℝ)
    (s : I ⊕ Fin n) : (LXm M lam W s).totalDegree ≤ d := by
  cases s with
  | inl j => exact hR.2.2.2.2.1 j
  | inr i =>
    simp only [LXm, Sum.elim_inr]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine totalDegree_finset_sum_le (fun q _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact hR.2.2.2.2.2 q

lemma LXm_eval (M : Mod n I J S G) (lam : ℝ) (W : J × Fin n → ℝ)
    (P : MvPolynomial (I ⊕ Fin n) ℝ) (x : Fin n → ℝ) :
    eval x (aeval (LXm M lam W) P) = Fm M P lam W x := by
  rw [eval_aeval']
  unfold Fm
  have h : (fun s => eval x (LXm M lam W s)) = Sum.elim (M.b x) (fun i => lam * zv W (M.ps x) i) := by
    funext s
    cases s with
    | inl j => simp [LXm, Mod.b]
    | inr i => simp [LXm, zv, Mod.ps]
  rw [h]

end model

/-! ## §6 The model functions are `PF` families -/

section facts

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]
  (M : Mod n I J S G) {d : ℕ} (hR : Reg M d) {K : ℕ} (P : MvPolynomial (I ⊕ Fin n) ℝ)
  (hP : P.totalDegree ≤ K)

include hR hP

/-! ### In `W`, for a fixed scale -/

theorem pf_Fs (lam : ℝ) :
    PF K (fun (a : S × G) (W : J × Fin n → ℝ) => Fs M P lam W a.1 a.2) := by
  have h := PF.of_aeval (fun a : S × G => LWm M lam (M.X a)) (fun a s => LWm_deg M lam _ s)
    (fun s => LWm_mbp M hR lam s) P hP
  simp only [LWm_eval] at h
  exact h

theorem pf_msl (lam : ℝ) : PF K (fun (p : S) (W : J × Fin n → ℝ) => msl M P lam W p) := by
  have := hR.2.1
  exact pf_gm M.ga (pf_Fs M hR P hP lam)

theorem pf_Ysl (lam : ℝ) : PF (2 * K) (fun (p : S) (W : J × Fin n → ℝ) => Ysl M P lam W p) := by
  have := hR.2.1
  exact pf_gY M.ga (pf_Fs M hR P hP lam)

theorem pf_Bm (lam : ℝ) : PF K (fun (_ : Unit) (W : J × Fin n → ℝ) => Bm M P lam W) := by
  have := hR.1
  have := hR.2.1
  exact pf_gB M.pi M.ga (pf_Fs M hR P hP lam)

theorem pf_Vdn (lam : ℝ) : PF (2 * K) (fun (_ : Unit) (W : J × Fin n → ℝ) => Vdn M P lam W) := by
  have := hR.1
  have := hR.2.1
  exact pf_gVd M.pi M.ga (pf_Fs M hR P hP lam)

theorem pf_Vm (lam : ℝ) : PF (2 * K) (fun (_ : Unit) (W : J × Fin n → ℝ) => Vm M P lam W) := by
  have := hR.1
  have := hR.2.1
  exact pf_gV M.pi M.ga (pf_Fs M hR P hP lam)

/-- `Φ_lam` at the points of the model is measurable and bounded. -/
theorem mb_Phi (lam : ℝ) : MB (fun a : S × G => Phi M P lam (M.X a)) :=
  (pf_Fs M hR P hP lam).mb_integral

/-- `g_p` is measurable and bounded. -/
theorem mb_gsl : MB (fun p : S => gsl M P p) := by
  have := hR.2.1
  exact (mb_Phi M hR P hP 1).integral_right M.ga

/-- `m_p − g_p` as a family in `W`. -/
theorem pf_esl (lam : ℝ) :
    PF K (fun (p : S) (W : J × Fin n → ℝ) => msl M P lam W p - gsl M P p) :=
  (pf_msl M hR P hP lam).sub ((PF.const (mb_gsl M hR P hP)).mono (Nat.zero_le K))

theorem pf_Esl (lam : ℝ) : PF (2 * K) (fun (_ : Unit) (W : J × Fin n → ℝ) => Esl M P lam W) := by
  have := hR.1
  have h := ((pf_esl M hR P hP lam).mul (pf_esl M hR P hP lam)).unit M.pi
  rw [two_mul]
  have e : (fun (_ : Unit) (W : J × Fin n → ℝ) => Esl M P lam W) = fun (_ : Unit) W =>
      ∫ p, (msl M P lam W p - gsl M P p) * (msl M P lam W p - gsl M P p) ∂M.pi := by
    funext _ W
    unfold Esl
    simp only [sq]
  rw [e]
  exact h

/-! ### In the scale, for a fixed `W` -/

theorem pf_FsL (W : J × Fin n → ℝ) :
    PF K (fun (a : S × G) (l : Unit → ℝ) => Fs M P (l ()) W a.1 a.2) := by
  have h := PF.of_aeval (fun a : S × G => LRm M W (M.X a)) (fun a s => LRm_deg M W _ s)
    (fun s => LRm_mbp M hR W s) P hP
  simp only [LRm_eval] at h
  exact h

theorem pf_mslL (W : J × Fin n → ℝ) :
    PF K (fun (p : S) (l : Unit → ℝ) => msl M P (l ()) W p) := by
  have := hR.2.1
  exact pf_gm M.ga (pf_FsL M hR P hP W)

theorem pf_YslL (W : J × Fin n → ℝ) :
    PF (2 * K) (fun (p : S) (l : Unit → ℝ) => Ysl M P (l ()) W p) := by
  have := hR.2.1
  exact pf_gY M.ga (pf_FsL M hR P hP W)

theorem pf_BmL (W : J × Fin n → ℝ) :
    PF K (fun (_ : Unit) (l : Unit → ℝ) => Bm M P (l ()) W) := by
  have := hR.1
  have := hR.2.1
  exact pf_gB M.pi M.ga (pf_FsL M hR P hP W)

theorem pf_VdnL (W : J × Fin n → ℝ) :
    PF (2 * K) (fun (_ : Unit) (l : Unit → ℝ) => Vdn M P (l ()) W) := by
  have := hR.1
  have := hR.2.1
  exact pf_gVd M.pi M.ga (pf_FsL M hR P hP W)

theorem pf_VmL (W : J × Fin n → ℝ) :
    PF (2 * K) (fun (_ : Unit) (l : Unit → ℝ) => Vm M P (l ()) W) := by
  have := hR.1
  have := hR.2.1
  exact pf_gV M.pi M.ga (pf_FsL M hR P hP W)

theorem pf_eslL (W : J × Fin n → ℝ) :
    PF K (fun (p : S) (l : Unit → ℝ) => msl M P (l ()) W p - gsl M P p) :=
  (pf_mslL M hR P hP W).sub ((PF.const (mb_gsl M hR P hP)).mono (Nat.zero_le K))

/-- `lam ↦ Esl` is a polynomial of degree `≤ 2K` too. -/
theorem pf_EslL (W : J × Fin n → ℝ) :
    PF (2 * K) (fun (_ : Unit) (l : Unit → ℝ) => Esl M P (l ()) W) := by
  have := hR.1
  have h := ((pf_eslL M hR P hP W).mul (pf_eslL M hR P hP W)).unit M.pi
  rw [two_mul]
  have e : (fun (_ : Unit) (l : Unit → ℝ) => Esl M P (l ()) W) = fun (_ : Unit) l =>
      ∫ p, (msl M P (l ()) W p - gsl M P p) * (msl M P (l ()) W p - gsl M P p) ∂M.pi := by
    funext _ l
    unfold Esl
    simp only [sq]
  rw [e]
  exact h

/-! ### Corollaries -/

/-- For a fixed `W` and scale, `F` is bounded on the model. -/
theorem Fs_bounded (lam : ℝ) (W : J × Fin n → ℝ) : ∃ C : ℝ, ∀ p g, |Fs M P lam W p g| ≤ C := by
  obtain ⟨C, hC⟩ := ((pf_Fs M hR P hP lam).mb W).2
  exact ⟨C, fun p g => hC (p, g)⟩

/-- Joint measurability of `(W, p, g) ↦ F`. -/
theorem meas_Fs (lam : ℝ) :
    Measurable (fun a : (J × Fin n → ℝ) × (S × G) => Fs M P lam a.1 a.2.1 a.2.2) := by
  obtain ⟨c, hc, he⟩ := (pf_Fs M hR P hP lam).expansion
  have e : (fun a : (J × Fin n → ℝ) × (S × G) => Fs M P lam a.1 a.2.1 a.2.2) =
      fun a => ∑ m ∈ expSet (J × Fin n) K, c m a.2 * monv m a.1 := by
    funext a
    exact he a.2 a.1
  rw [e]
  exact Finset.measurable_sum _ (fun m _ =>
    ((hc m).1.comp measurable_snd).mul ((measurable_monv m).comp measurable_fst))

/-- The law of total variance: `V = Vdn + E_p (m_p − B)²`. -/
theorem Vm_decomp (lam : ℝ) (W : J × Fin n → ℝ) :
    Vm M P lam W = Vdn M P lam W + ∫ p, (msl M P lam W p - Bm M P lam W) ^ 2 ∂M.pi := by
  have := hR.1
  have := hR.2.1
  exact gV_decomp M.pi M.ga (pf_Fs M hR P hP lam) W

/-- `Y_p = E_g F² − m_p²`. -/
theorem Ysl_eq (lam : ℝ) (W : J × Fin n → ℝ) (p : S) :
    Ysl M P lam W p = msl M (P * P) lam W p - msl M P lam W p ^ 2 := by
  have := hR.2.1
  have h := gY_eq M.ga (pf_Fs M hR P hP lam) p W
  have e : (fun (a : S × G) (W : J × Fin n → ℝ) => Fs M P lam W a.1 a.2 * Fs M P lam W a.1 a.2) =
      fun a W => Fs M (P * P) lam W a.1 a.2 := by
    funext a W
    unfold Fs Fm
    rw [map_mul]
  rw [e] at h
  exact h

/-- `V = B(P²) − B(P)²`. -/
theorem Vm_eq (lam : ℝ) (W : J × Fin n → ℝ) :
    Vm M P lam W = Bm M (P * P) lam W - Bm M P lam W ^ 2 := by
  have := hR.1
  have := hR.2.1
  have h := gV_eq M.pi M.ga (pf_Fs M hR P hP lam) W
  have e : (fun (a : S × G) (W : J × Fin n → ℝ) => Fs M P lam W a.1 a.2 * Fs M P lam W a.1 a.2) =
      fun a W => Fs M (P * P) lam W a.1 a.2 := by
    funext a W
    unfold Fs Fm
    rw [map_mul]
  rw [e] at h
  exact h

/-- `E_W m_p = E_g Φ_lam`. -/
theorem int_msl (lam : ℝ) (p : S) :
    ∫ W, msl M P lam W p ∂stdGauss (J × Fin n) = ∫ g, Phi M P lam (M.X (p, g)) ∂M.ga := by
  have := hR.2.1
  exact ((pf_Fs M hR P hP lam).comp
    (measurable_prodMk_left (x := p) : Measurable fun g : G => (p, g))).fubini M.ga

/-- `E_W B = E_p E_W m_p`. -/
theorem int_Bm (lam : ℝ) :
    ∫ W, Bm M P lam W ∂stdGauss (J × Fin n) =
      ∫ p, ∫ W, msl M P lam W p ∂stdGauss (J × Fin n) ∂M.pi := by
  have := hR.1
  exact (pf_msl M hR P hP lam).fubini M.pi

/-- `E_W Vdn = E_p E_W Y_p`. -/
theorem int_Vdn (lam : ℝ) :
    ∫ W, Vdn M P lam W ∂stdGauss (J × Fin n) =
      ∫ p, ∫ W, Ysl M P lam W p ∂stdGauss (J × Fin n) ∂M.pi := by
  have := hR.1
  exact (pf_Ysl M hR P hP lam).fubini M.pi

/-- `E_W Esl = E_p E_W (m_p − g_p)²`. -/
theorem int_Esl (lam : ℝ) :
    ∫ W, Esl M P lam W ∂stdGauss (J × Fin n) =
      ∫ p, ∫ W, (msl M P lam W p - gsl M P p) ^ 2 ∂stdGauss (J × Fin n) ∂M.pi := by
  have := hR.1
  exact ((pf_esl M hR P hP lam).pow 2).fubini M.pi

omit hP in
/-- **Polynomial structure and regularity** of the model functions. -/
theorem polyFacts : PolyFacts M d := by
  intro K P hP
  refine ⟨fun lam W => ?_, fun lam x => ?_, fun lam p => ?_, fun W p => ?_, fun W => ?_,
    fun W => ?_, fun W => ?_, fun lam => ?_⟩
  · exact ⟨aeval (LXm M lam W) P,
      (deg_aeval_mul _ d (LXm_deg M hR lam W) P).trans (Nat.mul_le_mul_left d hP),
      LXm_eval M lam W P⟩
  · exact ⟨aeval (LWm M lam x) P, (deg_aeval _ (LWm_deg M lam x) P).trans hP,
      LWm_eval M lam x P⟩
  · exact (pf_msl M hR P hP lam).exists_poly p
  · exact (pf_mslL M hR P hP W).exists_poly1 p
  · exact (pf_BmL M hR P hP W).exists_poly1 ()
  · exact (pf_VdnL M hR P hP W).exists_poly1 ()
  · exact (pf_VmL M hR P hP W).exists_poly1 ()
  · exact meas_Fs M hR P hP lam

end facts

end BstLean.Part86

#print axioms BstLean.Part86.polyFacts
#print axioms BstLean.Part86.Vm_decomp
#print axioms BstLean.Part86.pf_Esl
#print axioms BstLean.Part86.int_Esl
#print axioms BstLean.Part86.PF.fubini
