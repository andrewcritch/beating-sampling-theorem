import BstLean.Part86Defs
import BstLean.Part84Gauss
import BstLean.Part59LemmaQ_Gaussian

/-!
# Part 86, the Gaussian model given the anchors (`gaussModel86`)

Assembly of `GaussModel86` from slice decorrelation, the pointwise scale comparison, the slice
reverse Hölder inequality, and the fourth-moment constant.
-/

namespace BstLean.Part86.XGauss

open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open BstLean.Part29 (stdGauss)
open BstLean.Part78 (zv)
open BstLean.Part84 (Fourth84 sq_shift_integral sq_integral_le var_le_sq)

/-! ## Polynomially dominated functions -/

section tame

variable {ι : Type} [Fintype ι]

/-- The dominating function `(1 + ‖W‖²)^N`. -/
noncomputable def Dom (N : ℕ) (W : ι → ℝ) : ℝ := (1 + ∑ a, W a ^ 2) ^ N

lemma one_le_base (W : ι → ℝ) : 1 ≤ 1 + ∑ a, W a ^ 2 := by
  have := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => sq_nonneg (W a)); linarith

lemma one_le_Dom (N : ℕ) (W : ι → ℝ) : 1 ≤ Dom N W := one_le_pow₀ (one_le_base W)

lemma Dom_pos (N : ℕ) (W : ι → ℝ) : 0 < Dom N W := lt_of_lt_of_le one_pos (one_le_Dom N W)

lemma Dom_mul (N N' : ℕ) (W : ι → ℝ) : Dom N W * Dom N' W = Dom (N + N') W :=
  (pow_add _ _ _).symm

lemma Dom_mono {N N' : ℕ} (h : N ≤ N') (W : ι → ℝ) : Dom N W ≤ Dom N' W :=
  pow_le_pow_right₀ (one_le_base W) h

lemma Dom_meas (N : ℕ) : Measurable (Dom N : (ι → ℝ) → ℝ) := by unfold Dom; fun_prop

lemma Dom_integrable (N : ℕ) : Integrable (Dom N : (ι → ℝ) → ℝ) (stdGauss ι) := by
  have h := BstLean.Part59.gaussian_eval_integrable59x
    ((1 + ∑ a : ι, MvPolynomial.X a ^ 2) ^ N : MvPolynomial ι ℝ)
  have e : (Dom N : (ι → ℝ) → ℝ) = fun z => (1 + ∑ x, z x ^ 2) ^ N := rfl
  rw [e]
  simpa using h

lemma abs_le_Dom (W : ι → ℝ) (a : ι) : |W a| ≤ Dom 1 W := by
  unfold Dom
  rw [pow_one]
  have h1 : W a ^ 2 ≤ ∑ a, W a ^ 2 :=
    Finset.single_le_sum (f := fun a => W a ^ 2) (fun a _ => sq_nonneg _) (Finset.mem_univ a)
  have h2 : |W a| ≤ 1 + W a ^ 2 := by
    rw [← sq_abs]; nlinarith [sq_nonneg (|W a| - 1), abs_nonneg (W a)]
  linarith

/-- `h` is jointly measurable and polynomially dominated in `W`, uniformly in `t`. -/
def Tame {T : Type} [MeasurableSpace T] (h : (ι → ℝ) → T → ℝ) : Prop :=
  Measurable (fun a : (ι → ℝ) × T => h a.1 a.2) ∧
    ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧ ∀ W t, |h W t| ≤ A * Dom N W

variable {T T' : Type} [MeasurableSpace T] [MeasurableSpace T']

lemma Tame.add {h1 h2 : (ι → ℝ) → T → ℝ} (H1 : Tame h1) (H2 : Tame h2) :
    Tame (fun W t => h1 W t + h2 W t) := by
  obtain ⟨m1, A1, N1, a1, b1⟩ := H1
  obtain ⟨m2, A2, N2, a2, b2⟩ := H2
  refine ⟨m1.add m2, A1 + A2, N1 + N2, by linarith, fun W t => ?_⟩
  have e1 := Dom_mono (Nat.le_add_right N1 N2) W
  have e2 := Dom_mono (Nat.le_add_left N2 N1) W
  calc |h1 W t + h2 W t| ≤ |h1 W t| + |h2 W t| := abs_add_le _ _
    _ ≤ A1 * Dom N1 W + A2 * Dom N2 W := add_le_add (b1 W t) (b2 W t)
    _ ≤ A1 * Dom (N1 + N2) W + A2 * Dom (N1 + N2) W :=
      add_le_add (mul_le_mul_of_nonneg_left e1 a1) (mul_le_mul_of_nonneg_left e2 a2)
    _ = (A1 + A2) * Dom (N1 + N2) W := by ring

lemma Tame.mul {h1 h2 : (ι → ℝ) → T → ℝ} (H1 : Tame h1) (H2 : Tame h2) :
    Tame (fun W t => h1 W t * h2 W t) := by
  obtain ⟨m1, A1, N1, a1, b1⟩ := H1
  obtain ⟨m2, A2, N2, a2, b2⟩ := H2
  refine ⟨m1.mul m2, A1 * A2, N1 + N2, mul_nonneg a1 a2, fun W t => ?_⟩
  rw [abs_mul, ← Dom_mul]
  calc |h1 W t| * |h2 W t| ≤ (A1 * Dom N1 W) * (A2 * Dom N2 W) :=
        mul_le_mul (b1 W t) (b2 W t) (abs_nonneg _) (mul_nonneg a1 (Dom_pos _ _).le)
    _ = A1 * A2 * (Dom N1 W * Dom N2 W) := by ring

lemma Tame.const (c : ℝ) : Tame (fun (_ : ι → ℝ) (_ : T) => c) :=
  ⟨measurable_const, |c|, 0, abs_nonneg _, fun W _ => by simp [Dom]⟩

lemma Tame.neg {h : (ι → ℝ) → T → ℝ} (H : Tame h) : Tame (fun W t => - h W t) := by
  obtain ⟨m, A, N, a, b⟩ := H
  exact ⟨m.neg, A, N, a, fun W t => by rw [abs_neg]; exact b W t⟩

lemma Tame.sub {h1 h2 : (ι → ℝ) → T → ℝ} (H1 : Tame h1) (H2 : Tame h2) :
    Tame (fun W t => h1 W t - h2 W t) := by
  have := H1.add H2.neg
  simpa [sub_eq_add_neg] using this

lemma Tame.pow {h : (ι → ℝ) → T → ℝ} (H : Tame h) (j : ℕ) : Tame (fun W t => h W t ^ j) := by
  induction j with
  | zero => simpa using Tame.const (ι := ι) (T := T) 1
  | succ j ih => simpa [pow_succ] using ih.mul H

lemma Tame.comp_right {h : (ι → ℝ) → T → ℝ} (H : Tame h) {φ : T' → T} (hφ : Measurable φ) :
    Tame (fun W t' => h W (φ t')) := by
  obtain ⟨m, A, N, a, b⟩ := H
  exact ⟨m.comp (measurable_fst.prodMk (hφ.comp measurable_snd)), A, N, a, fun W t => b W _⟩

lemma Tame.integrable {h : (ι → ℝ) → T → ℝ} (H : Tame h) (τ : Measure T) [IsFiniteMeasure τ] :
    Integrable (fun a : (ι → ℝ) × T => h a.1 a.2) ((stdGauss ι).prod τ) := by
  obtain ⟨m, A, N, a, b⟩ := H
  have hd : Integrable (fun a : (ι → ℝ) × T => A * Dom N a.1) ((stdGauss ι).prod τ) :=
    ((Dom_integrable N).const_mul A).comp_fst τ
  refine hd.mono' m.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]; exact b _ _

lemma Tame.int_left {h : (ι → ℝ) → T → ℝ} (H : Tame h) (t : T) :
    Integrable (fun W => h W t) (stdGauss ι) := by
  obtain ⟨m, A, N, a, b⟩ := H
  refine ((Dom_integrable N).const_mul A).mono'
    (m.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]; exact b _ _

lemma Tame.int_right {h : (ι → ℝ) → T → ℝ} (H : Tame h) (W : ι → ℝ) (τ : Measure T)
    [IsFiniteMeasure τ] : Integrable (h W) τ := by
  obtain ⟨m, A, N, a, b⟩ := H
  refine (integrable_const (A * Dom N W)).mono'
    (m.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]; exact b _ _

lemma Tame.swap {h : (ι → ℝ) → T → ℝ} (H : Tame h) (τ : Measure T) [IsFiniteMeasure τ] :
    ∫ W, ∫ t, h W t ∂τ ∂stdGauss ι = ∫ t, ∫ W, h W t ∂stdGauss ι ∂τ :=
  integral_integral_swap (H.integrable τ)

/-- Integrate out the second factor of the parameter. -/
lemma Tame.intR {T1 T2 : Type} [MeasurableSpace T1] [MeasurableSpace T2]
    {h : (ι → ℝ) → T1 × T2 → ℝ} (H : Tame h) (τ : Measure T2) [IsProbabilityMeasure τ] :
    Tame (fun W t1 => ∫ t2, h W (t1, t2) ∂τ) := by
  obtain ⟨m, A, N, a, b⟩ := H
  refine ⟨?_, A, N, a, fun W t1 => ?_⟩
  · have hm : Measurable (fun z : ((ι → ℝ) × T1) × T2 => h z.1.1 (z.1.2, z.2)) :=
      m.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := τ)).measurable
  · have := norm_integral_le_of_norm_le_const (μ := τ) (f := fun t2 => h W (t1, t2))
      (C := A * Dom N W) (Filter.Eventually.of_forall fun t2 => by
        rw [Real.norm_eq_abs]; exact b _ _)
    simpa using this

/-- Integrate out `W`: the result is a bounded measurable function of the parameter. -/
lemma Tame.intW {h : (ι → ℝ) → T → ℝ} (H : Tame h) :
    Tame (ι := ι) (fun _ t => ∫ W, h W t ∂stdGauss ι) := by
  have Hi := H
  obtain ⟨m, A, N, a, b⟩ := H
  refine ⟨?_, A * ∫ W, Dom N W ∂stdGauss ι, 0,
    mul_nonneg a (integral_nonneg fun W => (Dom_pos N W).le), fun _ t => ?_⟩
  · exact (m.stronglyMeasurable.integral_prod_left' (μ := stdGauss ι)).measurable.comp
      measurable_snd
  · have h1 : |∫ W, h W t ∂stdGauss ι| ≤ ∫ W, A * Dom N W ∂stdGauss ι := by
      refine (abs_integral_le_integral_abs).trans ?_
      exact integral_mono (Hi.int_left t).abs ((Dom_integrable N).const_mul A) (fun W => b W t)
    rw [integral_const_mul] at h1
    simpa [Dom] using h1

/-- Restrict a tame function on `S × G` to a slice. -/
lemma Tame.slice {T1 T2 : Type} [MeasurableSpace T1] [MeasurableSpace T2]
    {h : (ι → ℝ) → T1 × T2 → ℝ} (H : Tame h) (p : T1) : Tame (fun W g => h W (p, g)) :=
  H.comp_right measurable_prodMk_left

/-- Integrate out the whole parameter. -/
lemma Tame.intAll {h : (ι → ℝ) → T → ℝ} (H : Tame h) (τ : Measure T) [IsProbabilityMeasure τ] :
    Tame (fun W (_ : Unit) => ∫ t, h W t ∂τ) :=
  (H.comp_right (measurable_snd : Measurable (Prod.snd : Unit × T → T))).intR τ

/-- A function of the parameter only that comes from a tame function is integrable. -/
lemma Tame.int_par {c : T → ℝ} (H : Tame (ι := ι) (fun _ t => c t)) (τ : Measure T)
    [IsFiniteMeasure τ] : Integrable c τ := H.int_right 0 τ

end tame

/-! ## General facts -/

lemma var_shift {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) (c : ℝ) :
    ∫ x, (f x - c) ^ 2 ∂μ = ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ + (∫ y, f y ∂μ - c) ^ 2 := by
  rw [(sq_shift_integral μ f hf hf2 c).2, (sq_shift_integral μ f hf hf2 _).2]; ring

lemma cs_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) (h1 h2 : α → ℝ)
    (i11 : Integrable (fun x => h1 x ^ 2) μ) (i22 : Integrable (fun x => h2 x ^ 2) μ)
    (i12 : Integrable (fun x => h1 x * h2 x) μ) :
    (∫ x, h1 x * h2 x ∂μ) ^ 2 ≤ (∫ x, h1 x ^ 2 ∂μ) * ∫ x, h2 x ^ 2 ∂μ := by
  have key : ∀ t : ℝ, 0 ≤ (∫ x, h1 x ^ 2 ∂μ) * (t * t) + (-2 * ∫ x, h1 x * h2 x ∂μ) * t +
      ∫ x, h2 x ^ 2 ∂μ := by
    intro t
    have e : ∫ x, (t * h1 x - h2 x) ^ 2 ∂μ =
        t ^ 2 * ∫ x, h1 x ^ 2 ∂μ - 2 * t * ∫ x, h1 x * h2 x ∂μ + ∫ x, h2 x ^ 2 ∂μ := by
      have e0 : (fun x => (t * h1 x - h2 x) ^ 2) =
          fun x => t ^ 2 * h1 x ^ 2 - 2 * t * (h1 x * h2 x) + h2 x ^ 2 := by funext x; ring
      have a1 : ∫ x, (t ^ 2 * h1 x ^ 2 - 2 * t * (h1 x * h2 x) + h2 x ^ 2) ∂μ =
          ∫ x, (t ^ 2 * h1 x ^ 2 - 2 * t * (h1 x * h2 x)) ∂μ + ∫ x, h2 x ^ 2 ∂μ :=
        integral_add ((i11.const_mul _).sub (i12.const_mul _)) i22
      have a2 : ∫ x, (t ^ 2 * h1 x ^ 2 - 2 * t * (h1 x * h2 x)) ∂μ =
          ∫ x, t ^ 2 * h1 x ^ 2 ∂μ - ∫ x, 2 * t * (h1 x * h2 x) ∂μ :=
        integral_sub (i11.const_mul _) (i12.const_mul _)
      rw [e0, a1, a2, integral_const_mul, integral_const_mul]
    have h0 : 0 ≤ ∫ x, (t * h1 x - h2 x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    rw [e] at h0
    nlinarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

lemma eval_bound {σ : Type} (P : MvPolynomial σ ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (y : σ → ℝ) (R : ℝ), 1 ≤ R → (∀ c, |y c| ≤ R) →
      |MvPolynomial.eval y P| ≤ A * R ^ P.totalDegree := by
  refine ⟨∑ m ∈ P.support, |P.coeff m|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro y R hR hy
  rw [MvPolynomial.eval_eq, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [abs_mul, Finset.abs_prod]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ∏ i ∈ m.support, |y i ^ m i| ≤ ∏ i ∈ m.support, R ^ m i := by
        gcongr with i hi
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hy i) _
    _ = R ^ (∑ i ∈ m.support, m i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ R ^ P.totalDegree := pow_le_pow_right₀ hR (MvPolynomial.le_totalDegree hm)

/-! ## The model functions are tame -/

section main

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

lemma tameFs (M : Mod n I J S G) (d : ℕ) (hR : Reg M d) (hPF : PolyFacts M d)
    (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ) :
    Tame (fun (W : J × Fin n → ℝ) (s : S × G) => Fs M P lam W s.1 s.2) := by
  classical
  refine ⟨(hPF P.totalDegree P le_rfl).2.2.2.2.2.2.2 lam, ?_⟩
  obtain ⟨AP, hAP0, hAP⟩ := eval_bound P
  choose Ab hAb0 hAb using fun j => eval_bound (M.bP j)
  choose Ap hAp0 hAp using fun q => eval_bound (M.psP q)
  set Cb := ∑ j, Ab j with hCb
  set Cp := ∑ q, Ap q with hCp
  have hCb0 : 0 ≤ Cb := Finset.sum_nonneg fun j _ => hAb0 j
  have hCp0 : 0 ≤ Cp := Finset.sum_nonneg fun j _ => hAp0 j
  set B := 1 + Cb + |lam| * (Fintype.card J) * Cp with hB
  have hB1 : 1 ≤ B := by
    have : 0 ≤ |lam| * (Fintype.card J) * Cp := by positivity
    linarith
  refine ⟨AP * B ^ P.totalDegree, P.totalDegree, by positivity, fun W s => ?_⟩
  have hx : ∀ c, |M.X (s.1, s.2) c| ≤ 1 := by
    intro c
    have h1 := hR.2.2.2.1 (s.1, s.2)
    have h2 : M.X (s.1, s.2) c ^ 2 ≤ ∑ i, M.X (s.1, s.2) i ^ 2 :=
      Finset.single_le_sum (f := fun i => M.X (s.1, s.2) i ^ 2) (fun a _ => sq_nonneg _)
        (Finset.mem_univ c)
    exact (sq_le_one_iff_abs_le_one _).1 (h2.trans h1)
  have hb : ∀ j, |M.b (M.X (s.1, s.2)) j| ≤ Cb := by
    intro j
    have h := hAb j _ 1 le_rfl hx
    rw [one_pow, mul_one] at h
    exact h.trans (Finset.single_le_sum (f := Ab) (fun a _ => hAb0 a) (Finset.mem_univ j))
  have hp : ∀ q, |M.ps (M.X (s.1, s.2)) q| ≤ Cp := by
    intro q
    have h := hAp q _ 1 le_rfl hx
    rw [one_pow, mul_one] at h
    exact h.trans (Finset.single_le_sum (f := Ap) (fun a _ => hAp0 a) (Finset.mem_univ q))
  have hD1 := one_le_Dom 1 W
  have hy : ∀ c, |Sum.elim (M.b (M.X (s.1, s.2)))
      (fun i => lam * zv W (M.ps (M.X (s.1, s.2))) i) c| ≤ B * Dom 1 W := by
    intro c
    have hBD : B ≤ B * Dom 1 W := by nlinarith
    rcases c with j | i
    · simp only [Sum.elim_inl]
      have : Cb ≤ B := by
        have : 0 ≤ |lam| * (Fintype.card J) * Cp := by positivity
        linarith
      exact (hb j).trans (this.trans hBD)
    · simp only [Sum.elim_inr]
      rw [abs_mul]
      have hz : |zv W (M.ps (M.X (s.1, s.2))) i| ≤ (Fintype.card J) * Cp * Dom 1 W := by
        unfold zv
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have : ∀ q ∈ (Finset.univ : Finset J),
            |W (q, i) * M.ps (M.X (s.1, s.2)) q| ≤ Dom 1 W * Cp := by
          intro q _
          rw [abs_mul]
          exact mul_le_mul (abs_le_Dom W _) (hp q) (abs_nonneg _) (by linarith)
        refine (Finset.sum_le_sum this).trans ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        apply le_of_eq; ring
      calc |lam| * |zv W (M.ps (M.X (s.1, s.2))) i|
          ≤ |lam| * ((Fintype.card J) * Cp * Dom 1 W) :=
            mul_le_mul_of_nonneg_left hz (abs_nonneg _)
        _ = (|lam| * (Fintype.card J) * Cp) * Dom 1 W := by ring
        _ ≤ B * Dom 1 W := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            linarith
  have h1R : 1 ≤ B * Dom 1 W := by nlinarith
  have h := hAP _ _ h1R hy
  have e : (B * Dom 1 W) ^ P.totalDegree = B ^ P.totalDegree * Dom P.totalDegree W := by
    rw [mul_pow]; unfold Dom; rw [pow_one]
  rw [e] at h
  calc |Fs M P lam W s.1 s.2| ≤ AP * (B ^ P.totalDegree * Dom P.totalDegree W) := h
    _ = AP * B ^ P.totalDegree * Dom P.totalDegree W := by ring

/-! ## Slice quantities -/

section slices

variable (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ)

/-- `m̄_p = E_W m_p`. -/
noncomputable def mbar (p : S) : ℝ := ∫ W, msl M P lam W p ∂stdGauss (J × Fin n)

/-- `Q_p(W) = E_g (F − m̄_p)²`. -/
noncomputable def Qf (W : J × Fin n → ℝ) (p : S) : ℝ :=
  ∫ g, (Fs M P lam W p g - mbar M P lam p) ^ 2 ∂M.ga

/-- `q_p = E_W Q_p`. -/
noncomputable def qsl (p : S) : ℝ := ∫ W, Qf M P lam W p ∂stdGauss (J × Fin n)

/-- `L_p = E_g Var_W F`. -/
noncomputable def Lsl (p : S) : ℝ :=
  ∫ g, ∫ W, (Fs M P lam W p g - Phi M P lam (M.X (p, g))) ^ 2 ∂stdGauss (J × Fin n) ∂M.ga

/-- `v_p = Var_W m_p`. -/
noncomputable def vsl (p : S) : ℝ :=
  ∫ W, (msl M P lam W p - mbar M P lam p) ^ 2 ∂stdGauss (J × Fin n)

/-- `R_p = E_g (Φ − m̄_p)²`. -/
noncomputable def Rsl (p : S) : ℝ :=
  ∫ g, (Phi M P lam (M.X (p, g)) - mbar M P lam p) ^ 2 ∂M.ga

variable [IsProbabilityMeasure M.pi] [IsProbabilityMeasure M.ga]
variable (hT : ∀ (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ),
  Tame (fun (W : J × Fin n → ℝ) (s : S × G) => Fs M P lam W s.1 s.2))

include hT

lemma t_Phi : Tame (ι := J × Fin n) (fun _ (s : S × G) => Phi M P lam (M.X s)) :=
  (hT P lam).intW

lemma t_msl : Tame (fun (W : J × Fin n → ℝ) (p : S) => msl M P lam W p) :=
  (hT P lam).intR M.ga

lemma t_mbar : Tame (ι := J × Fin n) (fun _ (p : S) => mbar M P lam p) :=
  (t_msl M P lam hT).intW

lemma t_Fc : Tame (fun (W : J × Fin n → ℝ) (s : S × G) =>
    Fs M P lam W s.1 s.2 - mbar M P lam s.1) :=
  (hT P lam).sub ((t_mbar M P lam hT).comp_right measurable_fst)

lemma t_Qf : Tame (fun (W : J × Fin n → ℝ) (p : S) => Qf M P lam W p) :=
  ((t_Fc M P lam hT).pow 2).intR M.ga

lemma t_q : Tame (ι := J × Fin n) (fun _ (p : S) => qsl M P lam p) :=
  (t_Qf M P lam hT).intW

lemma t_Fphi : Tame (fun (W : J × Fin n → ℝ) (s : S × G) =>
    Fs M P lam W s.1 s.2 - Phi M P lam (M.X s)) :=
  (hT P lam).sub (t_Phi M P lam hT)

lemma t_L : Tame (ι := J × Fin n) (fun _ (p : S) => Lsl M P lam p) :=
  (((t_Fphi M P lam hT).pow 2).intW).intR M.ga

lemma t_et : Tame (fun (W : J × Fin n → ℝ) (p : S) => msl M P lam W p - mbar M P lam p) :=
  (t_msl M P lam hT).sub (t_mbar M P lam hT)

lemma t_v : Tame (ι := J × Fin n) (fun _ (p : S) => vsl M P lam p) :=
  ((t_et M P lam hT).pow 2).intW

lemma t_Y : Tame (fun (W : J × Fin n → ℝ) (p : S) => Ysl M P lam W p) :=
  (((hT P lam).sub ((t_msl M P lam hT).comp_right measurable_fst)).pow 2).intR M.ga

lemma t_gsl : Tame (ι := J × Fin n) (fun _ (p : S) => gsl M P p) :=
  ((hT P 1).intW).intR M.ga

lemma mbar_eq (p : S) : mbar M P lam p = ∫ g, Phi M P lam (M.X (p, g)) ∂M.ga :=
  ((hT P lam).slice p).swap M.ga

lemma Lsl_nonneg (p : S) : 0 ≤ Lsl M P lam p :=
  integral_nonneg fun g => integral_nonneg fun W => sq_nonneg _

omit hT in
lemma Rsl_nonneg (p : S) : 0 ≤ Rsl M P lam p := integral_nonneg fun g => sq_nonneg _

lemma q_split (p : S) : qsl M P lam p = Lsl M P lam p + Rsl M P lam p := by
  have h1 : qsl M P lam p =
      ∫ g, ∫ W, (Fs M P lam W p g - mbar M P lam p) ^ 2 ∂stdGauss (J × Fin n) ∂M.ga :=
    (((t_Fc M P lam hT).pow 2).slice p).swap M.ga
  have h2 : ∀ g, ∫ W, (Fs M P lam W p g - mbar M P lam p) ^ 2 ∂stdGauss (J × Fin n) =
      ∫ W, (Fs M P lam W p g - Phi M P lam (M.X (p, g))) ^ 2 ∂stdGauss (J × Fin n) +
        (Phi M P lam (M.X (p, g)) - mbar M P lam p) ^ 2 := fun g =>
    var_shift (stdGauss (J × Fin n)) (fun W => Fs M P lam W p g) ((hT P lam).int_left (p, g))
      (((hT P lam).pow 2).int_left (p, g)) _
  have i1 : Integrable (fun g =>
      ∫ W, (Fs M P lam W p g - Phi M P lam (M.X (p, g))) ^ 2 ∂stdGauss (J × Fin n)) M.ga :=
    ((((t_Fphi M P lam hT).pow 2).intW).slice p).int_par M.ga
  have i2 : Integrable (fun g => (Phi M P lam (M.X (p, g)) - mbar M P lam p) ^ 2) M.ga :=
    ((((t_Phi M P lam hT).sub ((t_mbar M P lam hT).comp_right measurable_fst)).pow 2).slice
      p).int_par M.ga
  rw [h1]
  simp only [h2]
  exact integral_add i1 i2

lemma L_le_q (p : S) : Lsl M P lam p ≤ qsl M P lam p := by
  rw [q_split M P lam hT p]; linarith [Rsl_nonneg M P lam p]

lemma q_nonneg (p : S) : 0 ≤ qsl M P lam p :=
  (Lsl_nonneg M P lam hT p).trans (L_le_q M P lam hT p)

omit hT in
lemma v_nonneg (p : S) : 0 ≤ vsl M P lam p := integral_nonneg fun W => sq_nonneg _

lemma Ysl_eq (W : J × Fin n → ℝ) (p : S) :
    Ysl M P lam W p = Qf M P lam W p - (msl M P lam W p - mbar M P lam p) ^ 2 := by
  have hi := ((hT P lam).slice p).int_right W M.ga
  have hi2 := (((hT P lam).pow 2).slice p).int_right W M.ga
  have a1 := (sq_shift_integral M.ga (fun g => Fs M P lam W p g) hi hi2 (msl M P lam W p)).2
  have a2 := (sq_shift_integral M.ga (fun g => Fs M P lam W p g) hi hi2 (mbar M P lam p)).2
  have e : ∫ g, Fs M P lam W p g ∂M.ga = msl M P lam W p := rfl
  rw [e] at a1 a2
  unfold Ysl Qf
  rw [a1, a2]; ring

/-- The variance of `Q_p`. -/
lemma VQ_le (Lam CRH : ℝ) (D : ℕ) (hD : Decor86 M Lam) (hRH : SliceRH M D CRH)
    (hL : 0 ≤ Lam) (hC0 : 0 ≤ CRH) (hLC : Lam * CRH ≤ 1 / 2)
    (hpoly : ∀ W : J × Fin n → ℝ, ∃ Q : MvPolynomial (Fin n) ℝ, Q.totalDegree ≤ D ∧
      ∀ x, MvPolynomial.eval x Q = Fm M P lam W x) (p : S) :
    ∫ W, (Qf M P lam W p - qsl M P lam p) ^ 2 ∂stdGauss (J × Fin n) ≤
      2 * (Lam * CRH) * qsl M P lam p ^ 2 := by
  have tFc := t_Fc M P lam hT
  have e0 : ∀ (W : J × Fin n → ℝ) (x : Fin n → ℝ),
      Fm M ((P - MvPolynomial.C (mbar M P lam p)) ^ 2) lam W x =
        (Fm M P lam W x - mbar M P lam p) ^ 2 := by
    intro W x; unfold Fm; rw [map_pow, map_sub, MvPolynomial.eval_C]
  have hm : ∀ W, msl M ((P - MvPolynomial.C (mbar M P lam p)) ^ 2) lam W p = Qf M P lam W p := by
    intro W; unfold msl Qf Fs; simp only [e0]
  have hphi : ∀ g, Phi M ((P - MvPolynomial.C (mbar M P lam p)) ^ 2) lam (M.X (p, g)) =
      ∫ W', (Fs M P lam W' p g - mbar M P lam p) ^ 2 ∂stdGauss (J × Fin n) := by
    intro g; unfold Phi Fs; simp only [e0]
  have hfs : ∀ W g, Fs M ((P - MvPolynomial.C (mbar M P lam p)) ^ 2) lam W p g =
      (Fs M P lam W p g - mbar M P lam p) ^ 2 := fun W g => e0 W _
  have h := hD ((P - MvPolynomial.C (mbar M P lam p)) ^ 2) lam p
  simp only [hm, hphi, hfs] at h
  have hA : ∫ W, (Qf M P lam W p - qsl M P lam p) ^ 2 ∂stdGauss (J × Fin n) ≤
      Lam * ∫ g, ∫ W, ((Fs M P lam W p g - mbar M P lam p) ^ 2 -
        ∫ W', (Fs M P lam W' p g - mbar M P lam p) ^ 2 ∂stdGauss (J × Fin n)) ^ 2
        ∂stdGauss (J × Fin n) ∂M.ga := h
  -- step 2
  have h2 : ∀ g, ∫ W, ((Fs M P lam W p g - mbar M P lam p) ^ 2 -
        ∫ W', (Fs M P lam W' p g - mbar M P lam p) ^ 2 ∂stdGauss (J × Fin n)) ^ 2
        ∂stdGauss (J × Fin n) ≤
      ∫ W, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂stdGauss (J × Fin n) := by
    intro g
    have := var_le_sq (stdGauss (J × Fin n)) (fun W => (Fs M P lam W p g - mbar M P lam p) ^ 2)
      ((tFc.pow 2).int_left (p, g)) (((tFc.pow 2).pow 2).int_left (p, g))
    refine this.trans (le_of_eq ?_)
    congr 1; funext W; ring
  have i1 : Integrable (fun g => ∫ W, ((Fs M P lam W p g - mbar M P lam p) ^ 2 -
        ∫ W', (Fs M P lam W' p g - mbar M P lam p) ^ 2 ∂stdGauss (J × Fin n)) ^ 2
        ∂stdGauss (J × Fin n)) M.ga :=
    (((((tFc.pow 2).sub ((tFc.pow 2).intW)).pow 2).intW).slice p).int_par M.ga
  have i2 : Integrable (fun g =>
      ∫ W, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂stdGauss (J × Fin n)) M.ga :=
    (((tFc.pow 4).intW).slice p).int_par M.ga
  have hB := integral_mono i1 i2 h2
  have hsw : ∫ g, ∫ W, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂stdGauss (J × Fin n) ∂M.ga =
      ∫ W, ∫ g, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂M.ga ∂stdGauss (J × Fin n) :=
    (((tFc.pow 4).slice p).swap M.ga).symm
  have h3 : ∀ W, ∫ g, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂M.ga ≤
      CRH * Qf M P lam W p ^ 2 := by
    intro W
    obtain ⟨Q0, hdeg, hev⟩ := hpoly W
    have := hRH p (Q0 - MvPolynomial.C (mbar M P lam p))
      ((MvPolynomial.totalDegree_sub_C_le Q0 _).trans hdeg)
    simp only [map_sub, MvPolynomial.eval_C, hev] at this
    exact this
  have i3 : Integrable (fun W => ∫ g, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂M.ga)
      (stdGauss (J × Fin n)) := ((tFc.pow 4).intR M.ga).int_left p
  have tQ := t_Qf M P lam hT
  have i4 : Integrable (fun W => Qf M P lam W p ^ 2) (stdGauss (J × Fin n)) :=
    (tQ.pow 2).int_left p
  have hC := integral_mono i3 (i4.const_mul CRH) h3
  rw [integral_const_mul] at hC
  have hS := (sq_shift_integral (stdGauss (J × Fin n)) (fun W => Qf M P lam W p)
    (tQ.int_left p) i4 (qsl M P lam p)).2
  have hq : ∫ W, Qf M P lam W p ∂stdGauss (J × Fin n) = qsl M P lam p := rfl
  rw [hq] at hS
  have hV0 : 0 ≤ ∫ W, (Qf M P lam W p - qsl M P lam p) ^ 2 ∂stdGauss (J × Fin n) :=
    integral_nonneg fun W => sq_nonneg _
  set VQ := ∫ W, (Qf M P lam W p - qsl M P lam p) ^ 2 ∂stdGauss (J × Fin n)
  set S2 := ∫ W, Qf M P lam W p ^ 2 ∂stdGauss (J × Fin n)
  set I4 := ∫ g, ∫ W, (Fs M P lam W p g - mbar M P lam p) ^ 4 ∂stdGauss (J × Fin n) ∂M.ga
  have hI : I4 ≤ CRH * S2 := by rw [hsw]; exact hC
  have hVI : VQ ≤ Lam * I4 := hA.trans (mul_le_mul_of_nonneg_left hB hL)
  have hS2 : S2 = VQ + qsl M P lam p ^ 2 := by rw [hS]; ring
  have h5 : VQ ≤ Lam * CRH * (VQ + qsl M P lam p ^ 2) := by
    calc VQ ≤ Lam * I4 := hVI
      _ ≤ Lam * (CRH * S2) := mul_le_mul_of_nonneg_left hI hL
      _ = Lam * CRH * (VQ + qsl M P lam p ^ 2) := by rw [hS2]; ring
  have ha0 : 0 ≤ Lam * CRH := mul_nonneg hL hC0
  nlinarith [mul_nonneg hV0 (by linarith : (0 : ℝ) ≤ 1 / 2 - Lam * CRH),
    mul_nonneg ha0 (sq_nonneg (qsl M P lam p))]

/-- The variance of `Y_p`. -/
lemma VY_le (Lam CRH K4 : ℝ) (D k : ℕ) (hD : Decor86 M Lam) (hRH : SliceRH M D CRH)
    (h4 : Fourth84 k K4) (hL : 0 ≤ Lam) (hC0 : 0 ≤ CRH) (hLC : Lam * CRH ≤ 1 / 2)
    (hK : K4 * Lam ≤ CRH) (hK0 : 0 ≤ K4)
    (hpoly : ∀ W : J × Fin n → ℝ, ∃ Q : MvPolynomial (Fin n) ℝ, Q.totalDegree ≤ D ∧
      ∀ x, MvPolynomial.eval x Q = Fm M P lam W x) (p : S)
    (hpolyW : ∃ Q : MvPolynomial (J × Fin n) ℝ, Q.totalDegree ≤ k ∧
      ∀ W, MvPolynomial.eval W Q = msl M P lam W p) :
    ∫ W, (Ysl M P lam W p - (qsl M P lam p - vsl M P lam p)) ^ 2 ∂stdGauss (J × Fin n) ≤
      6 * (Lam * CRH) * qsl M P lam p ^ 2 := by
  have hVQ := VQ_le M P lam hT Lam CRH D hD hRH hL hC0 hLC hpoly p
  have tQ := t_Qf M P lam hT
  have tq := t_q M P lam hT
  have tv := t_v M P lam hT
  have te := t_et M P lam hT
  have tY := t_Y M P lam hT
  have iL : Integrable (fun W => (Ysl M P lam W p - (qsl M P lam p - vsl M P lam p)) ^ 2)
      (stdGauss (J × Fin n)) := ((tY.sub (tq.sub tv)).pow 2).int_left p
  have iQ : Integrable (fun W => (Qf M P lam W p - qsl M P lam p) ^ 2)
      (stdGauss (J × Fin n)) := ((tQ.sub tq).pow 2).int_left p
  have iE : Integrable (fun W => ((msl M P lam W p - mbar M P lam p) ^ 2 - vsl M P lam p) ^ 2)
      (stdGauss (J × Fin n)) := (((te.pow 2).sub tv).pow 2).int_left p
  have h1 : ∫ W, (Ysl M P lam W p - (qsl M P lam p - vsl M P lam p)) ^ 2
        ∂stdGauss (J × Fin n) ≤
      ∫ W, (2 * (Qf M P lam W p - qsl M P lam p) ^ 2 +
        2 * ((msl M P lam W p - mbar M P lam p) ^ 2 - vsl M P lam p) ^ 2)
        ∂stdGauss (J × Fin n) := by
    refine integral_mono iL ((iQ.const_mul 2).add (iE.const_mul 2)) (fun W => ?_)
    show (Ysl M P lam W p - (qsl M P lam p - vsl M P lam p)) ^ 2 ≤ _
    rw [Ysl_eq M P lam hT W p]
    nlinarith [sq_nonneg ((Qf M P lam W p - qsl M P lam p) +
      ((msl M P lam W p - mbar M P lam p) ^ 2 - vsl M P lam p))]
  have h1' : ∫ W, (2 * (Qf M P lam W p - qsl M P lam p) ^ 2 +
        2 * ((msl M P lam W p - mbar M P lam p) ^ 2 - vsl M P lam p) ^ 2)
        ∂stdGauss (J × Fin n) =
      2 * ∫ W, (Qf M P lam W p - qsl M P lam p) ^ 2 ∂stdGauss (J × Fin n) +
      2 * ∫ W, ((msl M P lam W p - mbar M P lam p) ^ 2 - vsl M P lam p) ^ 2
        ∂stdGauss (J × Fin n) := by
    rw [integral_add (iQ.const_mul 2) (iE.const_mul 2), integral_const_mul, integral_const_mul]
  have h2 : ∫ W, ((msl M P lam W p - mbar M P lam p) ^ 2 - vsl M P lam p) ^ 2
        ∂stdGauss (J × Fin n) ≤
      ∫ W, (msl M P lam W p - mbar M P lam p) ^ 4 ∂stdGauss (J × Fin n) := by
    have := var_le_sq (stdGauss (J × Fin n)) (fun W => (msl M P lam W p - mbar M P lam p) ^ 2)
      ((te.pow 2).int_left p) (((te.pow 2).pow 2).int_left p)
    refine this.trans (le_of_eq ?_)
    congr 1; funext W; ring
  have h3 : ∫ W, (msl M P lam W p - mbar M P lam p) ^ 4 ∂stdGauss (J × Fin n) ≤
      K4 * vsl M P lam p ^ 2 := by
    obtain ⟨Q0, hdeg, hev⟩ := hpolyW
    have := h4 (J × Fin n) (Q0 - MvPolynomial.C (mbar M P lam p))
      ((MvPolynomial.totalDegree_sub_C_le Q0 _).trans hdeg)
    simp only [map_sub, MvPolynomial.eval_C, hev] at this
    exact this
  have hv0 := v_nonneg M P lam p
  have hq0 := q_nonneg M P lam hT p
  have hvq : vsl M P lam p ≤ Lam * qsl M P lam p :=
    (hD P lam p).trans (mul_le_mul_of_nonneg_left (L_le_q M P lam hT p) hL)
  have h6 : K4 * vsl M P lam p ^ 2 ≤ Lam * CRH * qsl M P lam p ^ 2 := by
    have a1 : vsl M P lam p ^ 2 ≤ (Lam * qsl M P lam p) ^ 2 := pow_le_pow_left₀ hv0 hvq 2
    have a2 : K4 * vsl M P lam p ^ 2 ≤ K4 * (Lam * qsl M P lam p) ^ 2 :=
      mul_le_mul_of_nonneg_left a1 hK0
    have a3 : K4 * (Lam * qsl M P lam p) ^ 2 = (K4 * Lam) * (Lam * qsl M P lam p ^ 2) := by ring
    have a4 : (K4 * Lam) * (Lam * qsl M P lam p ^ 2) ≤ CRH * (Lam * qsl M P lam p ^ 2) :=
      mul_le_mul_of_nonneg_right hK (mul_nonneg hL (sq_nonneg _))
    linarith
  linarith

/-- The slice error. -/
lemma E_le (Lam : ℝ) (k : ℕ) (hD : Decor86 M Lam) (hSc : Scale86 M k)
    (hP : P.totalDegree ≤ k) (hlam : |lam ^ 2 - 1| ≤ 1 / (n : ℝ)) (p : S) :
    ∫ W, (msl M P lam W p - gsl M P p) ^ 2 ∂stdGauss (J × Fin n) ≤
      (Lam + 2 / (n : ℝ)) * Lsl M P lam p := by
  have tm := t_msl M P lam hT
  have hs := var_shift (stdGauss (J × Fin n)) (fun W => msl M P lam W p) (tm.int_left p)
    ((tm.pow 2).int_left p) (gsl M P p)
  have hm : ∫ W, msl M P lam W p ∂stdGauss (J × Fin n) = mbar M P lam p := rfl
  rw [hm] at hs
  have tPP := (t_Phi M P lam hT).sub (t_Phi M P 1 hT)
  have i1 : Integrable (fun g => Phi M P lam (M.X (p, g)) - Phi M P 1 (M.X (p, g))) M.ga :=
    (tPP.slice p).int_par M.ga
  have i2 : Integrable (fun g => (Phi M P lam (M.X (p, g)) - Phi M P 1 (M.X (p, g))) ^ 2)
      M.ga := ((tPP.pow 2).slice p).int_par M.ga
  have iP : Integrable (fun g => Phi M P lam (M.X (p, g))) M.ga :=
    ((t_Phi M P lam hT).slice p).int_par M.ga
  have iP1 : Integrable (fun g => Phi M P 1 (M.X (p, g))) M.ga :=
    ((t_Phi M P 1 hT).slice p).int_par M.ga
  have hd : mbar M P lam p - gsl M P p =
      ∫ g, (Phi M P lam (M.X (p, g)) - Phi M P 1 (M.X (p, g))) ∂M.ga := by
    rw [integral_sub iP iP1, mbar_eq M P lam hT p]; rfl
  have h1 := sq_integral_le M.ga _ i1 i2
  have i3 : Integrable (fun g => 2 / (n : ℝ) *
      ∫ W, (Fs M P lam W p g - Phi M P lam (M.X (p, g))) ^ 2 ∂stdGauss (J × Fin n)) M.ga :=
    (((((t_Fphi M P lam hT).pow 2).intW).slice p).int_par M.ga).const_mul _
  have h2 := integral_mono i2 i3 (fun g => hSc P hP lam hlam (M.X (p, g)))
  rw [integral_const_mul] at h2
  have hL' : ∫ g, ∫ W, (Fs M P lam W p g - Phi M P lam (M.X (p, g))) ^ 2
      ∂stdGauss (J × Fin n) ∂M.ga = Lsl M P lam p := rfl
  have hDp : vsl M P lam p ≤ Lam * Lsl M P lam p := hD P lam p
  have hv : ∫ W, (msl M P lam W p - mbar M P lam p) ^ 2 ∂stdGauss (J × Fin n) =
      vsl M P lam p := rfl
  rw [hs, hv, hd]
  have h2' : ∫ g, (Phi M P lam (M.X (p, g)) - Phi M P 1 (M.X (p, g))) ^ 2 ∂M.ga ≤
      2 / (n : ℝ) * Lsl M P lam p := h2
  linarith

/-- The slice variance of `Φ₁`. -/
lemma R_le (k : ℕ) (hSc : Scale86 M k) (hn : 2 ≤ n)
    (hP : P.totalDegree ≤ k) (hlam : |lam ^ 2 - 1| ≤ 1 / (n : ℝ)) (p : S) :
    ∫ g, (Phi M P 1 (M.X (p, g)) - gsl M P p) ^ 2 ∂M.ga ≤ 2 * qsl M P lam p := by
  have t1 := t_Phi M P 1 hT
  have tl := t_Phi M P lam hT
  have tb := (t_mbar M P lam hT).comp_right (measurable_fst : Measurable (Prod.fst : S × G → S))
  have iP1 : Integrable (fun g => Phi M P 1 (M.X (p, g))) M.ga := (t1.slice p).int_par M.ga
  have iP1' : Integrable (fun g => Phi M P 1 (M.X (p, g)) ^ 2) M.ga :=
    ((t1.pow 2).slice p).int_par M.ga
  have hs := var_shift M.ga (fun g => Phi M P 1 (M.X (p, g))) iP1 iP1' (mbar M P lam p)
  have hg : ∫ g, Phi M P 1 (M.X (p, g)) ∂M.ga = gsl M P p := rfl
  rw [hg] at hs
  have iA : Integrable (fun g => (Phi M P 1 (M.X (p, g)) - mbar M P lam p) ^ 2) M.ga :=
    (((t1.sub tb).pow 2).slice p).int_par M.ga
  have iV : Integrable (fun g =>
      ∫ W, (Fs M P lam W p g - Phi M P lam (M.X (p, g))) ^ 2 ∂stdGauss (J × Fin n)) M.ga :=
    ((((t_Fphi M P lam hT).pow 2).intW).slice p).int_par M.ga
  have iR : Integrable (fun g => (Phi M P lam (M.X (p, g)) - mbar M P lam p) ^ 2) M.ga :=
    (((tl.sub tb).pow 2).slice p).int_par M.ga
  have hpt : ∀ g, (Phi M P 1 (M.X (p, g)) - mbar M P lam p) ^ 2 ≤
      2 * (2 / (n : ℝ) *
        ∫ W, (Fs M P lam W p g - Phi M P lam (M.X (p, g))) ^ 2 ∂stdGauss (J × Fin n)) +
      2 * (Phi M P lam (M.X (p, g)) - mbar M P lam p) ^ 2 := by
    intro g
    have h := hSc P hP lam hlam (M.X (p, g))
    have h' : (Phi M P lam (M.X (p, g)) - Phi M P 1 (M.X (p, g))) ^ 2 ≤ 2 / (n : ℝ) *
        ∫ W, (Fs M P lam W p g - Phi M P lam (M.X (p, g))) ^ 2 ∂stdGauss (J × Fin n) := h
    nlinarith [sq_nonneg ((Phi M P lam (M.X (p, g)) - Phi M P 1 (M.X (p, g))) +
      (Phi M P lam (M.X (p, g)) - mbar M P lam p))]
  have h1 : ∫ g, (Phi M P 1 (M.X (p, g)) - mbar M P lam p) ^ 2 ∂M.ga ≤
      ∫ g, (2 * (2 / (n : ℝ) *
        ∫ W, (Fs M P lam W p g - Phi M P lam (M.X (p, g))) ^ 2 ∂stdGauss (J × Fin n)) +
      2 * (Phi M P lam (M.X (p, g)) - mbar M P lam p) ^ 2) ∂M.ga :=
    integral_mono iA (((iV.const_mul _).const_mul 2).add (iR.const_mul 2)) hpt
  rw [integral_add ((iV.const_mul _).const_mul 2) (iR.const_mul 2), integral_const_mul,
    integral_const_mul, integral_const_mul] at h1
  have hL' : ∫ g, ∫ W, (Fs M P lam W p g - Phi M P lam (M.X (p, g))) ^ 2
      ∂stdGauss (J × Fin n) ∂M.ga = Lsl M P lam p := rfl
  have hR' : ∫ g, (Phi M P lam (M.X (p, g)) - mbar M P lam p) ^ 2 ∂M.ga = Rsl M P lam p := rfl
  rw [hL', hR'] at h1
  have hL0 := Lsl_nonneg M P lam hT p
  have hq := q_split M P lam hT p
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h4n : 2 * (2 / (n : ℝ)) ≤ 2 := by
    have : 2 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hnR
    linarith
  have h5 : 2 * (2 / (n : ℝ)) * Lsl M P lam p ≤ 2 * Lsl M P lam p :=
    mul_le_mul_of_nonneg_right h4n hL0
  have h0 : 0 ≤ (gsl M P p - mbar M P lam p) ^ 2 := sq_nonneg _
  nlinarith

end slices

/-! ## The Gaussian model -/

/-- **The Gaussian model given the anchors.** -/
theorem gaussModel86 (M : Mod n I J S G) (d k : ℕ) (Lam CRH K4 : ℝ) (hn : 2 ≤ n)
    (hR : Reg M d) (hPF : PolyFacts M d) (hD : Decor86 M Lam) (hSc : Scale86 M k)
    (hRH : SliceRH M (d * k) CRH) (h4 : Fourth84 k K4)
    (hL : 0 ≤ Lam) (hLC : Lam * CRH ≤ 1 / 2) (hK : K4 * Lam ≤ CRH) (hK0 : 0 ≤ K4)
    (hC0 : 0 ≤ CRH) :
    GaussModel86 M k (n * Lam + 2) (6 * n * Lam * CRH) Lam := by
  intro P hP lam hlam
  have := hR.1
  have := hR.2.1
  have hT := fun P lam => tameFs M d hR hPF P lam
  have hPFk := hPF k P hP
  have hpoly : ∀ W : J × Fin n → ℝ, ∃ Q : MvPolynomial (Fin n) ℝ, Q.totalDegree ≤ d * k ∧
      ∀ x, MvPolynomial.eval x Q = Fm M P lam W x := fun W => hPFk.1 lam W
  have hpolyW : ∀ p : S, ∃ Q : MvPolynomial (J × Fin n) ℝ, Q.totalDegree ≤ k ∧
      ∀ W, MvPolynomial.eval W Q = msl M P lam W p := fun p => hPFk.2.2.1 lam p
  have tq := t_q M P lam hT
  have tv := t_v M P lam hT
  have tL := t_L M P lam hT
  have tY := t_Y M P lam hT
  have tm := t_msl M P lam hT
  have tg := t_gsl M P hT
  have iq : Integrable (fun p => qsl M P lam p) M.pi := tq.int_par M.pi
  have iv : Integrable (fun p => vsl M P lam p) M.pi := tv.int_par M.pi
  have iL : Integrable (fun p => Lsl M P lam p) M.pi := tL.int_par M.pi
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hLv0 : 0 ≤ ∫ p, qsl M P lam p ∂M.pi := integral_nonneg (q_nonneg M P lam hT)
  have hvq : ∀ p, vsl M P lam p ≤ Lam * qsl M P lam p := fun p =>
    (hD P lam p).trans (mul_le_mul_of_nonneg_left (L_le_q M P lam hT p) hL)
  have tE : Tame (fun (W : J × Fin n → ℝ) (p : S) => (msl M P lam W p - gsl M P p) ^ 2) :=
    (tm.sub tg).pow 2
  have tVd : Tame (fun (W : J × Fin n → ℝ) (_ : Unit) => Vdn M P lam W) := tY.intAll M.pi
  refine ⟨∫ p, qsl M P lam p ∂M.pi, ∫ p, (qsl M P lam p - vsl M P lam p) ∂M.pi, hLv0,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← integral_const_mul]
    exact integral_mono (iq.const_mul _) (iq.sub iv) (fun p => by
      have := hvq p
      show (1 - Lam) * qsl M P lam p ≤ qsl M P lam p - vsl M P lam p
      linarith)
  · exact (tE.intAll M.pi).int_left ()
  · exact ((tVd.sub (Tame.const _)).pow 2).int_left ()
  · have sw : ∫ W, Esl M P lam W ∂stdGauss (J × Fin n) =
        ∫ p, ∫ W, (msl M P lam W p - gsl M P p) ^ 2 ∂stdGauss (J × Fin n) ∂M.pi := tE.swap M.pi
    rw [sw]
    have hc : 0 ≤ Lam + 2 / (n : ℝ) := by positivity
    have h1 : ∫ p, ∫ W, (msl M P lam W p - gsl M P p) ^ 2 ∂stdGauss (J × Fin n) ∂M.pi ≤
        ∫ p, (Lam + 2 / (n : ℝ)) * Lsl M P lam p ∂M.pi :=
      integral_mono (tE.intW.int_par M.pi) (iL.const_mul _)
        (fun p => E_le M P lam hT Lam k hD hSc hP hlam p)
    rw [integral_const_mul] at h1
    have h2 : ∫ p, Lsl M P lam p ∂M.pi ≤ ∫ p, qsl M P lam p ∂M.pi :=
      integral_mono iL iq (L_le_q M P lam hT)
    have e : ((n : ℝ) * Lam + 2) / n = Lam + 2 / (n : ℝ) := by field_simp
    rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hc)
  · set Vb := ∫ p, (qsl M P lam p - vsl M P lam p) ∂M.pi with hVb
    set Lv := ∫ p, qsl M P lam p ∂M.pi with hLv
    have th : Tame (fun (W : J × Fin n → ℝ) (p : S) =>
        Ysl M P lam W p - (qsl M P lam p - vsl M P lam p)) := tY.sub (tq.sub tv)
    have tH : Tame (fun (W : J × Fin n → ℝ) (z : S × S) =>
        (Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1)) *
        (Ysl M P lam W z.2 - (qsl M P lam z.2 - vsl M P lam z.2))) :=
      (th.comp_right measurable_fst).mul (th.comp_right measurable_snd)
    have e1 : ∀ W, (Vdn M P lam W - Vb) ^ 2 =
        ∫ z, (Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1)) *
          (Ysl M P lam W z.2 - (qsl M P lam z.2 - vsl M P lam z.2)) ∂(M.pi.prod M.pi) := by
      intro W
      have a : Vdn M P lam W - Vb =
          ∫ p, (Ysl M P lam W p - (qsl M P lam p - vsl M P lam p)) ∂M.pi :=
        (integral_sub (tY.int_right W M.pi) (iq.sub iv)).symm
      have b := integral_prod_mul (μ := M.pi) (ν := M.pi)
        (fun p => Ysl M P lam W p - (qsl M P lam p - vsl M P lam p))
        (fun p => Ysl M P lam W p - (qsl M P lam p - vsl M P lam p))
      rw [a, sq]; exact b.symm
    simp only [e1]
    rw [tH.swap (M.pi.prod M.pi)]
    have hc0 : 0 ≤ 6 * (Lam * CRH) := by positivity
    have hpt : ∀ z : S × S, ∫ W, (Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1)) *
          (Ysl M P lam W z.2 - (qsl M P lam z.2 - vsl M P lam z.2)) ∂stdGauss (J × Fin n) ≤
        6 * (Lam * CRH) * (qsl M P lam z.1 * qsl M P lam z.2) := by
      intro z
      have hcs := cs_sq (stdGauss (J × Fin n))
        (fun W => Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1))
        (fun W => Ysl M P lam W z.2 - (qsl M P lam z.2 - vsl M P lam z.2))
        ((th.pow 2).int_left z.1) ((th.pow 2).int_left z.2) (tH.int_left z)
      have hA := VY_le M P lam hT Lam CRH K4 (d * k) k hD hRH h4 hL hC0 hLC hK hK0 hpoly z.1
        (hpolyW z.1)
      have hB := VY_le M P lam hT Lam CRH K4 (d * k) k hD hRH h4 hL hC0 hLC hK hK0 hpoly z.2
        (hpolyW z.2)
      have hq1 := q_nonneg M P lam hT z.1
      have hq2 := q_nonneg M P lam hT z.2
      have hA0 : 0 ≤ ∫ W, (Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1)) ^ 2
          ∂stdGauss (J × Fin n) := integral_nonneg fun W => sq_nonneg _
      have hX : 0 ≤ 6 * (Lam * CRH) * (qsl M P lam z.1 * qsl M P lam z.2) := by positivity
      have hprod := mul_le_mul hA hB (integral_nonneg fun W => sq_nonneg _)
        (by positivity : 0 ≤ 6 * (Lam * CRH) * qsl M P lam z.1 ^ 2)
      have hsq : (∫ W, (Ysl M P lam W z.1 - (qsl M P lam z.1 - vsl M P lam z.1)) *
          (Ysl M P lam W z.2 - (qsl M P lam z.2 - vsl M P lam z.2)) ∂stdGauss (J × Fin n)) ^ 2 ≤
          (6 * (Lam * CRH) * (qsl M P lam z.1 * qsl M P lam z.2)) ^ 2 := by
        refine (hcs.trans hprod).trans (le_of_eq ?_); ring
      exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq hsq hX)
    have iR : Integrable (fun z : S × S => qsl M P lam z.1 * qsl M P lam z.2)
        (M.pi.prod M.pi) :=
      ((tq.comp_right measurable_fst).mul (tq.comp_right measurable_snd)).int_par
        (M.pi.prod M.pi)
    have h1 := integral_mono (tH.intW.int_par (M.pi.prod M.pi)) (iR.const_mul _) hpt
    rw [integral_const_mul, integral_prod_mul (μ := M.pi) (ν := M.pi)
      (fun p => qsl M P lam p) (fun p => qsl M P lam p)] at h1
    have e : 6 * (n : ℝ) * Lam * CRH / n * Lv ^ 2 = 6 * (Lam * CRH) * (Lv * Lv) := by
      field_simp
    rw [e]; exact h1
  · have tR : Tame (ι := J × Fin n) (fun _ (s : S × G) =>
        (Phi M P 1 (M.X s) - gsl M P s.1) ^ 2) :=
      ((t_Phi M P 1 hT).sub (tg.comp_right measurable_fst)).pow 2
    have h1 : R1 M P ≤ ∫ p, 2 * qsl M P lam p ∂M.pi :=
      integral_mono ((tR.intR M.ga).int_par M.pi) (iq.const_mul 2)
        (fun p => R_le M P lam hT k hSc hn hP hlam p)
    rw [integral_const_mul] at h1
    exact h1

end main

end BstLean.Part86.XGauss

#print axioms BstLean.Part86.XGauss.gaussModel86
