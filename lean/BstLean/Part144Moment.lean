import BstLean.Part142Spread

/-!
# Part 144, sample moments: the first and second moments of `|Σ_j ξ_j|²`

Role: `delegations/statements/p144-spec.md`, item 1 (the moment part). Paper source: round onW15c
§2. Abstract setting: `μ` a probability measure on `Ω`, `z : Ω → ι → ℝ` bounded and measurable,
`m = meanV μ z`, `C = covV μ z` (Part 139), `ξ = z − m` (`cen`), and `k` independent samples
`us : Fin k → Ω` with the distribution `Measure.pi (fun _ => μ)`.

* `sumC`: `S_i = Σ_j ξ(u_j)_i`; `sqS`: `|S|²`; `trC = tr C`; `frC = Σ_{ij} C_ij²`;
  `radV`: the variance of the centred radius `|ξ|²`.
* `sqS_bm`: `|S|²` is bounded and measurable.
* `sqS_mean`: `E|S|² = k·tr C`.
* `sqS_var`: `E(|S|² − k·tr C)² = k·radV + 2k(k − 1)·frC`.
* `dist_decomp`: `(tr C − c)² + radV/2 + frC ≤ E(|z(u) − z(u′)|²/2 − c)²` (equality holds).
* `quadS_mean`: `E SᵀCS = k·frC`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144

open MeasureTheory ProbabilityTheory Set
open BstLean.Part139

/-! ## Tools -/

section tools

lemma bm_eval {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {f : Ω → ℝ} (hf : BM f) (j : Fin k) :
    BM (fun us : Fin k → Ω => f (us j)) :=
  ⟨hf.1.comp (measurable_pi_apply j), hf.2.imp fun _ h us => h (us j)⟩

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma int_fst (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a : α → ℝ) : ∫ p : α × β, a p.1 ∂(μ.prod ν) = ∫ x, a x ∂μ := by
  have h := integral_prod_mul (μ := μ) (ν := ν) a (fun _ : β => (1 : ℝ))
  simpa using h

lemma int_snd (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (b : β → ℝ) : ∫ p : α × β, b p.2 ∂(μ.prod ν) = ∫ y, b y ∂ν := by
  have h := integral_prod_mul (μ := μ) (ν := ν) (fun _ : α => (1 : ℝ)) b
  simpa using h

/-- The integral of `(a + 2b + c)²` for bounded measurable functions. -/
lemma int_sq3 (ν : Measure α) [IsFiniteMeasure ν] {a b c : α → ℝ}
    (ha : BM a) (hb : BM b) (hc : BM c) :
    ∫ x, (a x + 2 * b x + c x) ^ 2 ∂ν =
      ∫ x, a x ^ 2 ∂ν + 4 * ∫ x, b x ^ 2 ∂ν + ∫ x, c x ^ 2 ∂ν + 4 * ∫ x, a x * b x ∂ν +
        2 * ∫ x, a x * c x ∂ν + 4 * ∫ x, c x * b x ∂ν := by
  have e : (fun x => (a x + 2 * b x + c x) ^ 2) = fun x =>
      a x ^ 2 + 4 * b x ^ 2 + c x ^ 2 + 4 * (a x * b x) + 2 * (a x * c x) + 4 * (c x * b x) := by
    funext x; ring
  have i1 : Integrable (fun x => a x ^ 2) ν := ha.sq.integrable ν
  have i2 : Integrable (fun x => 4 * b x ^ 2) ν := (hb.sq.integrable ν).const_mul 4
  have i3 : Integrable (fun x => c x ^ 2) ν := hc.sq.integrable ν
  have i4 : Integrable (fun x => 4 * (a x * b x)) ν := ((ha.mul hb).integrable ν).const_mul 4
  have i5 : Integrable (fun x => 2 * (a x * c x)) ν := ((ha.mul hc).integrable ν).const_mul 2
  have i6 : Integrable (fun x => 4 * (c x * b x)) ν := ((hc.mul hb).integrable ν).const_mul 4
  have j2 : Integrable (fun x => a x ^ 2 + 4 * b x ^ 2) ν := i1.add i2
  have j3 : Integrable (fun x => a x ^ 2 + 4 * b x ^ 2 + c x ^ 2) ν := j2.add i3
  have j4 : Integrable (fun x => a x ^ 2 + 4 * b x ^ 2 + c x ^ 2 + 4 * (a x * b x)) ν := j3.add i4
  have j5 : Integrable (fun x => a x ^ 2 + 4 * b x ^ 2 + c x ^ 2 + 4 * (a x * b x) +
      2 * (a x * c x)) ν := j4.add i5
  rw [e, integral_add j5 i6, integral_add j4 i5, integral_add j3 i4, integral_add j2 i3,
    integral_add i1 i2]
  simp only [integral_const_mul]

end tools

/-! ## Definitions -/

section moment

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {ι : Type} [Fintype ι] (z : Ω → ι → ℝ)

/-- The centred vector `ξ = z − m`. -/
noncomputable def cen (ω : Ω) (i : ι) : ℝ := z ω i - meanV μ z i

/-- The centred sum `S_i = Σ_j (z(u_j)_i − m_i)`. -/
noncomputable def sumC (k : ℕ) (us : Fin k → Ω) (i : ι) : ℝ := ∑ j, (z (us j) i - meanV μ z i)

/-- `|S|²`. -/
noncomputable def sqS (k : ℕ) (us : Fin k → Ω) : ℝ := ∑ i, sumC μ z k us i ^ 2

/-- `tr C`. -/
noncomputable def trC : ℝ := ∑ i, covV μ z i i

/-- `Σ_{ij} C_ij²`. -/
noncomputable def frC : ℝ := ∑ i, ∑ j, covV μ z i j ^ 2

/-- The variance of the centred radius `|z − m|²`. -/
noncomputable def radV : ℝ := ∫ ω, (∑ i, (z ω i - meanV μ z i) ^ 2 - trC μ z) ^ 2 ∂μ

/-- The centred radius `ρ = |ξ|² − tr C`. -/
noncomputable def rad (ω : Ω) : ℝ := ∑ i, cen μ z ω i ^ 2 - trC μ z

/-- `ξ(u)·ξ(u′)`. -/
noncomputable def crossC (p : Ω × Ω) : ℝ := ∑ i, cen μ z p.1 i * cen μ z p.2 i

lemma radV_eq : radV μ z = ∫ ω, rad μ z ω ^ 2 ∂μ := rfl

lemma covV_eq (i j : ι) : ∫ ω, cen μ z ω i * cen μ z ω j ∂μ = covV μ z i j := rfl

/-- `Fin (k+1) → Ω` is `Ω × (Fin k → Ω)`. -/
lemma pi_succ (k : ℕ) (f : (Fin (k + 1) → Ω) → ℝ) :
    ∫ us, f us ∂Measure.pi (fun _ : Fin (k + 1) => μ) =
      ∫ p : Ω × (Fin k → Ω), f (Fin.cons (α := fun _ => Ω) p.1 p.2)
        ∂(μ.prod (Measure.pi fun _ : Fin k => μ)) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0
  have h2 := (MeasurePreserving.symm _ h).integral_comp' f
  rw [← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show f _ = f _
  congr 1
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;>
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero']

lemma sumC_cons (k : ℕ) (u : Ω) (us : Fin k → Ω) (i : ι) :
    sumC μ z (k + 1) (Fin.cons (α := fun _ => Ω) u us) i = cen μ z u i + sumC μ z k us i := by
  simp only [sumC, cen, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

section hyp

variable (hz : ∀ i, Measurable fun ω => z ω i) (hb : ∃ B : ℝ, ∀ ω i, |z ω i| ≤ B)
include hz hb

lemma cen_bm (i : ι) : BM (fun ω => cen μ z ω i) := by
  have h : BM (fun ω => z ω i) := ⟨hz i, hb.imp fun _ hB ω => hB ω i⟩
  exact h.sub (BM.const _)

lemma cen_int (i : ι) : ∫ ω, cen μ z ω i ∂μ = 0 := by
  have hzB : BM (fun ω => z ω i) := ⟨hz i, hb.imp fun _ hB ω => hB ω i⟩
  simp only [cen]
  rw [integral_sub (hzB.integrable μ) (integrable_const _), integral_const]
  simp [meanV]

lemma rad_bm : BM (rad μ z) :=
  (BM.sum Finset.univ fun i _ => (cen_bm μ z hz hb i).sq).sub (BM.const _)

lemma rad_int : ∫ ω, rad μ z ω ∂μ = 0 := by
  have hc := cen_bm μ z hz hb
  simp only [rad]
  rw [integral_sub ((BM.sum Finset.univ fun i _ => (hc i).sq).integrable μ) (integrable_const _),
    integral_finsetSum _ fun i _ => (hc i).sq.integrable μ, integral_const]
  have h : ∀ i, ∫ ω, cen μ z ω i ^ 2 ∂μ = covV μ z i i := fun i => by
    simp only [pow_two]; rfl
  simp [h, trC]

lemma sumC_bm (k : ℕ) (i : ι) : BM (fun us : Fin k → Ω => sumC μ z k us i) :=
  BM.sum _ fun j _ => bm_eval (cen_bm μ z hz hb i) j

/-- `|S|²` is bounded and measurable. -/
theorem sqS_bm (k : ℕ) : BM (sqS μ z k) :=
  BM.sum _ fun i _ => (sumC_bm μ z hz hb k i).sq

lemma sumC_int (k : ℕ) (i : ι) :
    ∫ us, sumC μ z k us i ∂Measure.pi (fun _ : Fin k => μ) = 0 := by
  induction k with
  | zero => simp [sumC]
  | succ k ih =>
    have i1 : Integrable (fun p : Ω × (Fin k → Ω) => cen μ z p.1 i)
        (μ.prod (Measure.pi fun _ : Fin k => μ)) := (cen_bm μ z hz hb i).fst.integrable _
    have i2 : Integrable (fun p : Ω × (Fin k → Ω) => sumC μ z k p.2 i)
        (μ.prod (Measure.pi fun _ : Fin k => μ)) := (sumC_bm μ z hz hb k i).snd.integrable _
    rw [pi_succ]
    simp only [sumC_cons]
    rw [integral_add i1 i2, int_fst μ _ (fun ω => cen μ z ω i),
      int_snd μ _ (fun us : Fin k → Ω => sumC μ z k us i), cen_int μ z hz hb, ih, add_zero]

lemma sumC_cov (k : ℕ) (i j : ι) :
    ∫ us, sumC μ z k us i * sumC μ z k us j ∂Measure.pi (fun _ : Fin k => μ) =
      k * covV μ z i j := by
  induction k with
  | zero => simp [sumC]
  | succ k ih =>
    have hc := cen_bm μ z hz hb
    have hs := sumC_bm μ z hz hb k
    set P := μ.prod (Measure.pi fun _ : Fin k => μ) with hP
    have e : (fun p : Ω × (Fin k → Ω) => (cen μ z p.1 i + sumC μ z k p.2 i) *
        (cen μ z p.1 j + sumC μ z k p.2 j)) = fun p =>
        (cen μ z p.1 i * cen μ z p.1 j) * 1 + cen μ z p.1 i * sumC μ z k p.2 j +
          cen μ z p.1 j * sumC μ z k p.2 i + 1 * (sumC μ z k p.2 i * sumC μ z k p.2 j) := by
      funext p; ring
    have i1 : Integrable (fun p : Ω × (Fin k → Ω) => (cen μ z p.1 i * cen μ z p.1 j) * 1) P :=
      (((hc i).mul (hc j)).fst.mul (BM.const 1)).integrable _
    have i2 : Integrable (fun p : Ω × (Fin k → Ω) => cen μ z p.1 i * sumC μ z k p.2 j) P :=
      ((hc i).fst.mul (hs j).snd).integrable _
    have i3 : Integrable (fun p : Ω × (Fin k → Ω) => cen μ z p.1 j * sumC μ z k p.2 i) P :=
      ((hc j).fst.mul (hs i).snd).integrable _
    have i4 : Integrable (fun p : Ω × (Fin k → Ω) =>
        1 * (sumC μ z k p.2 i * sumC μ z k p.2 j)) P :=
      ((BM.const 1).mul ((hs i).mul (hs j)).snd).integrable _
    have j2 : Integrable (fun p : Ω × (Fin k → Ω) => (cen μ z p.1 i * cen μ z p.1 j) * 1 +
        cen μ z p.1 i * sumC μ z k p.2 j) P := i1.add i2
    have j3 : Integrable (fun p : Ω × (Fin k → Ω) => (cen μ z p.1 i * cen μ z p.1 j) * 1 +
        cen μ z p.1 i * sumC μ z k p.2 j + cen μ z p.1 j * sumC μ z k p.2 i) P := j2.add i3
    rw [pi_succ]
    simp only [sumC_cons]
    rw [e, integral_add j3 i4, integral_add j2 i3, integral_add i1 i2, hP,
      integral_prod_mul (fun ω => cen μ z ω i * cen μ z ω j) (fun _ : Fin k → Ω => (1 : ℝ)),
      integral_prod_mul (fun ω => cen μ z ω i) (fun us : Fin k → Ω => sumC μ z k us j),
      integral_prod_mul (fun ω => cen μ z ω j) (fun us : Fin k → Ω => sumC μ z k us i),
      integral_prod_mul (fun _ : Ω => (1 : ℝ))
        (fun us : Fin k → Ω => sumC μ z k us i * sumC μ z k us j),
      ih, cen_int μ z hz hb, cen_int μ z hz hb, covV_eq]
    simp only [integral_const, probReal_univ, one_smul]
    push_cast
    ring

/-- **`E|S|² = k·tr C`.** -/
theorem sqS_mean (k : ℕ) :
    ∫ us, sqS μ z k us ∂Measure.pi (fun _ : Fin k => μ) = k * trC μ z := by
  simp only [sqS]
  rw [integral_finsetSum _ fun i _ => (sumC_bm μ z hz hb k i).sq.integrable _]
  simp only [pow_two, sumC_cov μ z hz hb k, trC, Finset.mul_sum]

/-- **`E SᵀCS = k·frC`.** -/
theorem quadS_mean (k : ℕ) :
    ∫ us, ∑ i, ∑ j, covV μ z i j * (sumC μ z k us i * sumC μ z k us j)
      ∂Measure.pi (fun _ : Fin k => μ) = k * frC μ z := by
  have hs := sumC_bm μ z hz hb k
  have hi : ∀ i j, Integrable (fun us : Fin k → Ω =>
      covV μ z i j * (sumC μ z k us i * sumC μ z k us j)) (Measure.pi fun _ : Fin k => μ) :=
    fun i j => (((hs i).mul (hs j)).integrable _).const_mul _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
  simp only [frC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hi i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, sumC_cov μ z hz hb k]
  ring

/-- **`E(|S|² − k·tr C)² = k·radV + 2k(k − 1)·frC`.** -/
theorem sqS_var (k : ℕ) :
    ∫ us, (sqS μ z k us - k * trC μ z) ^ 2 ∂Measure.pi (fun _ : Fin k => μ) =
      k * radV μ z + 2 * k * (k - 1) * frC μ z := by
  induction k with
  | zero => simp [sqS, sumC]
  | succ k ih =>
    have hc := cen_bm μ z hz hb
    have hs := sumC_bm μ z hz hb k
    have hr := rad_bm μ z hz hb
    set P := μ.prod (Measure.pi fun _ : Fin k => μ) with hP
    have hG : BM (fun us : Fin k → Ω => sqS μ z k us - (k : ℝ) * trC μ z) :=
      (sqS_bm μ z hz hb k).sub (BM.const _)
    have hGs : BM (fun p : Ω × (Fin k → Ω) => sqS μ z k p.2 - (k : ℝ) * trC μ z) := hG.snd
    have hB : BM (fun p : Ω × (Fin k → Ω) => ∑ i, cen μ z p.1 i * sumC μ z k p.2 i) :=
      BM.sum _ fun i _ => (hc i).fst.mul (hs i).snd
    have hrf : BM (fun p : Ω × (Fin k → Ω) => rad μ z p.1) := hr.fst
    have e : (fun p : Ω × (Fin k → Ω) =>
        (sqS μ z (k + 1) (Fin.cons (α := fun _ => Ω) p.1 p.2) - ((k + 1 : ℕ) : ℝ) * trC μ z) ^ 2) =
        fun p => ((sqS μ z k p.2 - (k : ℝ) * trC μ z) +
          2 * (∑ i, cen μ z p.1 i * sumC μ z k p.2 i) + rad μ z p.1) ^ 2 := by
      funext p
      congr 1
      simp only [sqS, sumC_cons, rad]
      have h : ∑ i, (cen μ z p.1 i + sumC μ z k p.2 i) ^ 2 = ∑ i, cen μ z p.1 i ^ 2 +
          2 * ∑ i, cen μ z p.1 i * sumC μ z k p.2 i + ∑ i, sumC μ z k p.2 i ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h]
      push_cast
      ring
    have key := int_sq3 P hGs hB hrf
    have I1 : ∫ p : Ω × (Fin k → Ω), (sqS μ z k p.2 - (k : ℝ) * trC μ z) ^ 2 ∂P =
        k * radV μ z + 2 * k * (k - 1) * frC μ z := by
      rw [hP, int_snd μ _ (fun us : Fin k → Ω => (sqS μ z k us - (k : ℝ) * trC μ z) ^ 2), ih]
    have I2 : ∫ p : Ω × (Fin k → Ω), (∑ i, cen μ z p.1 i * sumC μ z k p.2 i) ^ 2 ∂P =
        k * frC μ z := by
      have e2 : (fun p : Ω × (Fin k → Ω) => (∑ i, cen μ z p.1 i * sumC μ z k p.2 i) ^ 2) =
          fun p => ∑ i, ∑ j, (cen μ z p.1 i * cen μ z p.1 j) *
            (sumC μ z k p.2 i * sumC μ z k p.2 j) := by
        funext p
        rw [pow_two, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      have hi : ∀ i j, Integrable (fun p : Ω × (Fin k → Ω) => (cen μ z p.1 i * cen μ z p.1 j) *
          (sumC μ z k p.2 i * sumC μ z k p.2 j)) P := fun i j =>
        (((hc i).mul (hc j)).fst.mul ((hs i).mul (hs j)).snd).integrable _
      rw [e2, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
      simp only [frC, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hi i j]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hP, integral_prod_mul (fun ω => cen μ z ω i * cen μ z ω j)
        (fun us : Fin k → Ω => sumC μ z k us i * sumC μ z k us j), covV_eq,
        sumC_cov μ z hz hb k]
      ring
    have I3 : ∫ p : Ω × (Fin k → Ω), rad μ z p.1 ^ 2 ∂P = radV μ z := by
      rw [hP, int_fst μ _ (fun ω => rad μ z ω ^ 2), radV_eq]
    have I4 : ∫ p : Ω × (Fin k → Ω), (sqS μ z k p.2 - (k : ℝ) * trC μ z) *
        (∑ i, cen μ z p.1 i * sumC μ z k p.2 i) ∂P = 0 := by
      have e4 : (fun p : Ω × (Fin k → Ω) => (sqS μ z k p.2 - (k : ℝ) * trC μ z) *
          (∑ i, cen μ z p.1 i * sumC μ z k p.2 i)) = fun p => ∑ i, cen μ z p.1 i *
            ((sqS μ z k p.2 - (k : ℝ) * trC μ z) * sumC μ z k p.2 i) := by
        funext p
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hi : ∀ i, Integrable (fun p : Ω × (Fin k → Ω) => cen μ z p.1 i *
          ((sqS μ z k p.2 - (k : ℝ) * trC μ z) * sumC μ z k p.2 i)) P := fun i =>
        ((hc i).fst.mul (hG.mul (hs i)).snd).integrable _
      rw [e4, integral_finsetSum _ fun i _ => hi i]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hP, integral_prod_mul (fun ω => cen μ z ω i)
        (fun us : Fin k → Ω => (sqS μ z k us - (k : ℝ) * trC μ z) * sumC μ z k us i),
        cen_int μ z hz hb, zero_mul]
    have I5 : ∫ p : Ω × (Fin k → Ω), (sqS μ z k p.2 - (k : ℝ) * trC μ z) * rad μ z p.1 ∂P = 0 := by
      have e5 : (fun p : Ω × (Fin k → Ω) => (sqS μ z k p.2 - (k : ℝ) * trC μ z) * rad μ z p.1) =
          fun p => rad μ z p.1 * (sqS μ z k p.2 - (k : ℝ) * trC μ z) := by
        funext p; ring
      rw [e5, hP, integral_prod_mul (fun ω => rad μ z ω)
        (fun us : Fin k → Ω => sqS μ z k us - (k : ℝ) * trC μ z), rad_int μ z hz hb, zero_mul]
    have I6 : ∫ p : Ω × (Fin k → Ω), rad μ z p.1 *
        (∑ i, cen μ z p.1 i * sumC μ z k p.2 i) ∂P = 0 := by
      have e6 : (fun p : Ω × (Fin k → Ω) => rad μ z p.1 *
          (∑ i, cen μ z p.1 i * sumC μ z k p.2 i)) = fun p => ∑ i,
            (rad μ z p.1 * cen μ z p.1 i) * sumC μ z k p.2 i := by
        funext p
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hi : ∀ i, Integrable (fun p : Ω × (Fin k → Ω) =>
          (rad μ z p.1 * cen μ z p.1 i) * sumC μ z k p.2 i) P := fun i =>
        ((hr.mul (hc i)).fst.mul (hs i).snd).integrable _
      rw [e6, integral_finsetSum _ fun i _ => hi i]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hP, integral_prod_mul (fun ω => rad μ z ω * cen μ z ω i)
        (fun us : Fin k → Ω => sumC μ z k us i), sumC_int μ z hz hb, mul_zero]
    rw [pi_succ, e, key, I1, I2, I3, I4, I5, I6]
    push_cast
    ring

/-- **The distance and the three orthogonal parts**:
`(tr C − c)² + radV/2 + frC ≤ E(|z(u) − z(u′)|²/2 − c)²` (equality holds). -/
theorem dist_decomp (c : ℝ) :
    (trC μ z - c) ^ 2 + radV μ z / 2 + frC μ z ≤
      ∫ p : Ω × Ω, ((∑ i, (z p.1 i - z p.2 i) ^ 2) / 2 - c) ^ 2 ∂(μ.prod μ) := by
  have hc := cen_bm μ z hz hb
  have hr := rad_bm μ z hz hb
  have hX : BM (crossC μ z) := BM.sum _ fun i _ => (hc i).fst.mul (hc i).snd
  have hH : BM (fun p : Ω × Ω => rad μ z p.1 + rad μ z p.2) := hr.fst.add hr.snd
  have ha : BM (fun _ : Ω × Ω => trC μ z - c) := BM.const _
  have hb' : BM (fun p : Ω × Ω => -crossC μ z p / 2) := by
    have h := (BM.const (α := Ω × Ω) (-1 / 2)).mul hX
    have e : (fun p : Ω × Ω => -crossC μ z p / 2) = fun p => -1 / 2 * crossC μ z p := by
      funext p; ring
    rw [e]; exact h
  have hc' : BM (fun p : Ω × Ω => (rad μ z p.1 + rad μ z p.2) / 2) := by
    have h := (BM.const (α := Ω × Ω) (1 / 2)).mul hH
    have e : (fun p : Ω × Ω => (rad μ z p.1 + rad μ z p.2) / 2) =
        fun p => 1 / 2 * (rad μ z p.1 + rad μ z p.2) := by
      funext p; ring
    rw [e]; exact h
  have e : (fun p : Ω × Ω => ((∑ i, (z p.1 i - z p.2 i) ^ 2) / 2 - c) ^ 2) = fun p =>
      ((trC μ z - c) + 2 * (-crossC μ z p / 2) + (rad μ z p.1 + rad μ z p.2) / 2) ^ 2 := by
    funext p
    congr 1
    have h : ∑ i, (z p.1 i - z p.2 i) ^ 2 = ∑ i, cen μ z p.1 i ^ 2 + ∑ i, cen μ z p.2 i ^ 2 -
        2 * ∑ i, cen μ z p.1 i * cen μ z p.2 i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [cen]; ring
    rw [h]
    simp only [rad, crossC]
    ring
  have key := int_sq3 (μ.prod μ) ha hb' hc'
  -- the base integrals
  have IX : ∫ p, crossC μ z p ∂(μ.prod μ) = 0 := by
    simp only [crossC]
    rw [integral_finsetSum _ fun i _ => ((hc i).fst.mul (hc i).snd).integrable _]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_prod_mul (fun ω => cen μ z ω i) (fun ω => cen μ z ω i), cen_int μ z hz hb,
      zero_mul]
  have IX2 : ∫ p, crossC μ z p ^ 2 ∂(μ.prod μ) = frC μ z := by
    have e2 : (fun p : Ω × Ω => crossC μ z p ^ 2) = fun p => ∑ i, ∑ j,
        (cen μ z p.1 i * cen μ z p.1 j) * (cen μ z p.2 i * cen μ z p.2 j) := by
      funext p
      simp only [crossC]
      rw [pow_two, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hi : ∀ i j, Integrable (fun p : Ω × Ω => (cen μ z p.1 i * cen μ z p.1 j) *
        (cen μ z p.2 i * cen μ z p.2 j)) (μ.prod μ) := fun i j =>
      (((hc i).mul (hc j)).fst.mul ((hc i).mul (hc j)).snd).integrable _
    rw [e2, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
    simp only [frC]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hi i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_prod_mul (fun ω => cen μ z ω i * cen μ z ω j)
      (fun ω => cen μ z ω i * cen μ z ω j), covV_eq, pow_two]
  have IH : ∫ p : Ω × Ω, (rad μ z p.1 + rad μ z p.2) ∂(μ.prod μ) = 0 := by
    rw [integral_add (hr.fst.integrable _) (hr.snd.integrable _), int_fst μ μ (rad μ z),
      int_snd μ μ (rad μ z), rad_int μ z hz hb, add_zero]
  have IH2 : ∫ p : Ω × Ω, (rad μ z p.1 + rad μ z p.2) ^ 2 ∂(μ.prod μ) = 2 * radV μ z := by
    have e3 : (fun p : Ω × Ω => (rad μ z p.1 + rad μ z p.2) ^ 2) = fun p =>
        rad μ z p.1 ^ 2 + rad μ z p.2 ^ 2 + 2 * (rad μ z p.1 * rad μ z p.2) := by
      funext p; ring
    have i1 : Integrable (fun p : Ω × Ω => rad μ z p.1 ^ 2) (μ.prod μ) :=
      hr.sq.fst.integrable _
    have i2 : Integrable (fun p : Ω × Ω => rad μ z p.2 ^ 2) (μ.prod μ) :=
      hr.sq.snd.integrable _
    have i3 : Integrable (fun p : Ω × Ω => 2 * (rad μ z p.1 * rad μ z p.2)) (μ.prod μ) :=
      ((hr.fst.mul hr.snd).integrable _).const_mul 2
    have j2 : Integrable (fun p : Ω × Ω => rad μ z p.1 ^ 2 + rad μ z p.2 ^ 2) (μ.prod μ) :=
      i1.add i2
    rw [e3, integral_add j2 i3, integral_add i1 i2, int_fst μ μ (fun ω => rad μ z ω ^ 2),
      int_snd μ μ (fun ω => rad μ z ω ^ 2), integral_const_mul,
      integral_prod_mul (rad μ z) (rad μ z), rad_int μ z hz hb, ← radV_eq]
    ring
  have IHX : ∫ p : Ω × Ω, (rad μ z p.1 + rad μ z p.2) * crossC μ z p ∂(μ.prod μ) = 0 := by
    have e4 : (fun p : Ω × Ω => (rad μ z p.1 + rad μ z p.2) * crossC μ z p) = fun p =>
        ∑ i, ((rad μ z p.1 * cen μ z p.1 i) * cen μ z p.2 i +
          cen μ z p.1 i * (rad μ z p.2 * cen μ z p.2 i)) := by
      funext p
      simp only [crossC]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h1 : ∀ i, Integrable (fun p : Ω × Ω => (rad μ z p.1 * cen μ z p.1 i) * cen μ z p.2 i)
        (μ.prod μ) := fun i => ((hr.mul (hc i)).fst.mul (hc i).snd).integrable _
    have h2 : ∀ i, Integrable (fun p : Ω × Ω => cen μ z p.1 i * (rad μ z p.2 * cen μ z p.2 i))
        (μ.prod μ) := fun i => ((hc i).fst.mul (hr.mul (hc i)).snd).integrable _
    have h12 : ∀ i, Integrable (fun p : Ω × Ω => (rad μ z p.1 * cen μ z p.1 i) * cen μ z p.2 i +
        cen μ z p.1 i * (rad μ z p.2 * cen μ z p.2 i)) (μ.prod μ) := fun i => (h1 i).add (h2 i)
    rw [e4, integral_finsetSum _ fun i _ => h12 i]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_add (h1 i) (h2 i),
      integral_prod_mul (fun ω => rad μ z ω * cen μ z ω i) (fun ω => cen μ z ω i),
      integral_prod_mul (fun ω => cen μ z ω i) (fun ω => rad μ z ω * cen μ z ω i),
      cen_int μ z hz hb]
    simp
  -- the six terms
  have J1 : ∫ _p : Ω × Ω, (trC μ z - c) ^ 2 ∂(μ.prod μ) = (trC μ z - c) ^ 2 := by
    simp
  have J2 : ∫ p : Ω × Ω, (-crossC μ z p / 2) ^ 2 ∂(μ.prod μ) = frC μ z / 4 := by
    have e5 : (fun p : Ω × Ω => (-crossC μ z p / 2) ^ 2) = fun p => 1 / 4 * crossC μ z p ^ 2 := by
      funext p; ring
    rw [e5, integral_const_mul, IX2]; ring
  have J3 : ∫ p : Ω × Ω, ((rad μ z p.1 + rad μ z p.2) / 2) ^ 2 ∂(μ.prod μ) = radV μ z / 2 := by
    have e5 : (fun p : Ω × Ω => ((rad μ z p.1 + rad μ z p.2) / 2) ^ 2) =
        fun p => 1 / 4 * (rad μ z p.1 + rad μ z p.2) ^ 2 := by
      funext p; ring
    rw [e5, integral_const_mul, IH2]; ring
  have J4 : ∫ p : Ω × Ω, (trC μ z - c) * (-crossC μ z p / 2) ∂(μ.prod μ) = 0 := by
    have e5 : (fun p : Ω × Ω => (trC μ z - c) * (-crossC μ z p / 2)) =
        fun p => (-(trC μ z - c) / 2) * crossC μ z p := by
      funext p; ring
    rw [e5, integral_const_mul, IX, mul_zero]
  have J5 : ∫ p : Ω × Ω, (trC μ z - c) * ((rad μ z p.1 + rad μ z p.2) / 2) ∂(μ.prod μ) = 0 := by
    have e5 : (fun p : Ω × Ω => (trC μ z - c) * ((rad μ z p.1 + rad μ z p.2) / 2)) =
        fun p => ((trC μ z - c) / 2) * (rad μ z p.1 + rad μ z p.2) := by
      funext p; ring
    rw [e5, integral_const_mul, IH, mul_zero]
  have J6 : ∫ p : Ω × Ω, (rad μ z p.1 + rad μ z p.2) / 2 * (-crossC μ z p / 2) ∂(μ.prod μ) =
      0 := by
    have e5 : (fun p : Ω × Ω => (rad μ z p.1 + rad μ z p.2) / 2 * (-crossC μ z p / 2)) =
        fun p => (-1 / 4) * ((rad μ z p.1 + rad μ z p.2) * crossC μ z p) := by
      funext p; ring
    rw [e5, integral_const_mul, IHX, mul_zero]
  rw [e, key, J1, J2, J3, J4, J5, J6]
  linarith

end hyp

end moment

end BstLean.Part144

open BstLean.Part144 in
#print axioms sqS_bm
open BstLean.Part144 in
#print axioms sqS_mean
open BstLean.Part144 in
#print axioms sqS_var
open BstLean.Part144 in
#print axioms dist_decomp
open BstLean.Part144 in
#print axioms quadS_mean
