import BstLean.Part134All

/-!
# Part 149: the variance of a mean over a Gaussian field, for a test function that does not
depend on the input

Do not use `sorry`, `native_decide` or `axiom`.

Setting (as in `var_core` of Part 134): `G` a standard Gaussian `n × m` matrix (entries
`ξ (i, j)`), `e_u ∈ ℝ^m` a measurable family of vectors, each a unit vector or zero; `g` a bounded
measurable function on `ℝⁿ` (it does not depend on `u`).

* `mean_const`: `E_G E_u g(G e_u) = μ{e ≠ 0} · E_γ g + μ{e = 0} · g(0)`.
* `var_const`: `Var_G(E_u g(G e_u)) ≤ (|E_u e_u|² + E_{u,u'} ⟨e_u, e_{u'}⟩²) · Var_γ(g)`.
  This is a refinement of `var_core`: the frame constant `L` is replaced by the two-point
  quantity. Proof: the variance is `E_{u,u'} Cov(g(G e_u), g(G e_{u'}))` (`var_double`); the pair
  `(G e_u, G e_{u'})` has correlation `ρ = ⟨e_u, e_{u'}⟩` (`pair_law`), so the covariance is at
  most `ρ |c|² + ρ² a²` (`mehler2_sharp`; `c` the first chaos of `g`, `a² = Var g − |c|²`);
  `E_{u,u'} ρ = |E_u e_u|² ≥ 0`, `|c|² ≤ Var g` (`chaos1Bessel`) and `a² ≤ Var g`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105 (BM sC)
open BstLean.Part112 (chaos1Bessel)
open BstLean.Part130 BstLean.Part134

variable {n m : ℕ} {U : Type*} [MeasurableSpace U]

section varconst

variable (μ : Measure U) [IsProbabilityMeasure μ]

/-- The field `(u, ξ) ↦ g(G e_u)` is bounded measurable. -/
lemma bm_field {e : U → Fin m → ℝ} (hem : Measurable e) {g : (Fin n → ℝ) → ℝ} (hg : BM g) :
    BM (fun q : U × (Fin n × Fin m → ℝ) => g ((rowMat n (e q.1)).mulVec q.2)) := by
  have mZ : Measurable (fun q : U × (Fin n × Fin m → ℝ) => (rowMat n (e q.1)).mulVec q.2) := by
    simp_rw [rowMat_mulVec']
    exact measurable_mulVec_joint.comp
      ((measurable_unflat.comp measurable_snd).prodMk (hem.comp measurable_fst))
  exact hg.comp mZ

/-- For a unit vector `e`, `E_G g(G e) = E_γ g`. -/
lemma row_mean {e : Fin m → ℝ} (he : normSq e = 1) {g : (Fin n → ℝ) → ℝ} (hg : BM g) :
    ∫ ξ, g ((rowMat n e).mulVec ξ) ∂stdGauss (Fin n × Fin m) = ∫ z, g z ∂stdGauss (Fin n) := by
  have hm : Measurable (fun ξ : Fin n × Fin m → ℝ => (rowMat n e).mulVec ξ) :=
    measurable_mulVec_left _
  calc ∫ ξ, g ((rowMat n e).mulVec ξ) ∂stdGauss (Fin n × Fin m)
      = ∫ z, g z ∂(stdGauss (Fin n × Fin m)).map (fun ξ => (rowMat n e).mulVec ξ) :=
        (integral_map hm.aemeasurable hg.meas.aestronglyMeasurable).symm
    _ = _ := by rw [row_law he]

/-- **The mean.** `E_G E_u g(G e_u) = μ{e ≠ 0} · E_γ g + μ{e = 0} · g(0)`. -/
theorem mean_const {e : U → Fin m → ℝ} (hem : Measurable e)
    (he : ∀ u, normSq (e u) = 1 ∨ e u = 0) {g : (Fin n → ℝ) → ℝ} (hg : BM g) :
    ∫ ξ, (∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) ∂stdGauss (Fin n × Fin m) =
      μ.real {u | e u ≠ 0} * ∫ z, g z ∂stdGauss (Fin n) + μ.real {u | e u = 0} * g 0 := by
  classical
  have bF := bm_field (n := n) hem hg
  have hS : MeasurableSet {u | e u = 0} := hem (measurableSet_singleton 0)
  have hSc : MeasurableSet {u | e u ≠ 0} := hS.compl
  have e2 : ∫ ξ, (∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) ∂stdGauss (Fin n × Fin m) =
      ∫ u, (∫ ξ, g ((rowMat n (e u)).mulVec ξ) ∂stdGauss (Fin n × Fin m)) ∂μ :=
    integral_integral_swap (f := fun ξ u => g ((rowMat n (e u)).mulVec ξ))
      ((bF.comp measurable_swap).integrable ((stdGauss (Fin n × Fin m)).prod μ))
  have e3 : ∀ u, ∫ ξ, g ((rowMat n (e u)).mulVec ξ) ∂stdGauss (Fin n × Fin m) =
      {u | e u ≠ 0}.indicator (fun _ => ∫ z, g z ∂stdGauss (Fin n)) u +
        {u | e u = 0}.indicator (fun _ => g 0) u := by
    intro u
    by_cases h0 : e u = 0
    · have hc : ∀ ξ : Fin n × Fin m → ℝ, g ((rowMat n (e u)).mulVec ξ) = g 0 := by
        intro ξ
        rw [h0, rowMat_zero_mulVec]
      simp only [hc, integral_const]
      simp [h0]
    · have h1 : normSq (e u) = 1 := (he u).resolve_right h0
      rw [row_mean h1 hg]
      simp [h0]
  rw [e2]
  simp_rw [e3]
  rw [integral_add ((integrable_const _).indicator hSc) ((integrable_const _).indicator hS),
    integral_indicator_const _ hSc, integral_indicator_const _ hS]
  simp [smul_eq_mul]

/-- **The variance bound for a test function that does not depend on the input.** -/
theorem var_const {e : U → Fin m → ℝ} (hem : Measurable e)
    (he : ∀ u, normSq (e u) = 1 ∨ e u = 0) {g : (Fin n → ℝ) → ℝ} (hg : BM g) :
    ∫ ξ, (∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) ^ 2 ∂stdGauss (Fin n × Fin m) -
        (∫ ξ, (∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) ∂stdGauss (Fin n × Fin m)) ^ 2 ≤
      (∑ j, (∫ u, e u j ∂μ) ^ 2 +
          ∫ p, (∑ j, e p.1 j * e p.2 j) ^ 2 ∂(μ.prod μ)) *
        ∫ z, (g z - ∫ y, g y ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) := by
  classical
  set F : U × (Fin n × Fin m → ℝ) → ℝ := fun q => g ((rowMat n (e q.1)).mulVec q.2) with hFdef
  have bF : BM F := bm_field hem hg
  have hn1 : ∀ u, normSq (e u) ≤ 1 := by
    intro u
    rcases he u with h | h
    · exact h.le
    · rw [h]; simp [normSq]
  have be : ∀ j, BM (fun u => e u j) := by
    intro j
    refine ⟨(measurable_pi_apply j).comp hem, 1, fun u => ?_⟩
    have h1 : e u j ^ 2 ≤ normSq (e u) :=
      Finset.single_le_sum (f := fun j => e u j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : e u j ^ 2 ≤ 1 := h1.trans (hn1 u)
    exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)
  -- the statistics of `g`
  set mg : ℝ := ∫ y, g y ∂stdGauss (Fin n) with hmg
  set V : ℝ := ∫ z, (g z - mg) ^ 2 ∂stdGauss (Fin n) with hV
  set S : ℝ := ∑ i, (∫ z, g z * z i ∂stdGauss (Fin n)) ^ 2 with hS
  have hbes : S ≤ V := chaos1Bessel (Fin n) _ hg
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hV0 : 0 ≤ V := integral_nonneg fun z => sq_nonneg _
  -- the kernel
  set ρ : U × U → ℝ := fun p => ∑ j, e p.1 j * e p.2 j with hρ
  have bρ : BM ρ :=
    bm_sum Finset.univ fun j _ => ((be j).comp measurable_fst).mul ((be j).comp measurable_snd)
  set K : U × U → ℝ := fun p =>
    (∫ ξ, F (p.1, ξ) * F (p.2, ξ) ∂stdGauss (Fin n × Fin m)) -
      (∫ ξ, F (p.1, ξ) ∂stdGauss (Fin n × Fin m)) *
        (∫ ξ, F (p.2, ξ) ∂stdGauss (Fin n × Fin m)) with hK
  have bK : BM K := by
    have bH : BM (fun q : (U × U) × (Fin n × Fin m → ℝ) => F (q.1.1, q.2) * F (q.1.2, q.2)) :=
      (bF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
        (bF.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    have bA : BM (fun u => ∫ ξ, F (u, ξ) ∂stdGauss (Fin n × Fin m)) := bF.integral_right _
    exact (bH.integral_right _).sub ((bA.comp measurable_fst).mul (bA.comp measurable_snd))
  set J : U × U → ℝ := fun p => ρ p * S + ρ p ^ 2 * (V - S) with hJ
  have bJ : BM J := (bρ.mul (BM.const S)).add (bρ.sq.mul (BM.const (V - S)))
  have hpt : ∀ p, K p ≤ J p := by
    intro p
    have hzero : ∀ u u' : U, e u = 0 → ρ (u, u') = 0 ∧ ρ (u', u) = 0 := by
      intro u u' h
      simp [hρ, h]
    have hJ0 : ρ p = 0 → J p = 0 := by
      intro h0
      simp [hJ, h0]
    rcases he p.1 with h1 | h1
    · rcases he p.2 with h2 | h2
      · have hρ1 := abs_dot_le_one h1 h2
        have hm : Measurable (fun ξ : Fin n × Fin m → ℝ =>
            ((rowMat n (e p.1)).mulVec ξ, (rowMat n (e p.2)).mulVec ξ)) :=
          (measurable_mulVec_left _).prodMk (measurable_mulVec_left _)
        have bG : BM (fun q : (Fin n → ℝ) × (Fin n → ℝ) => g q.1 * g q.2) :=
          (hg.comp measurable_fst).mul (hg.comp measurable_snd)
        have hψ : Measurable (fun w : (Fin n → ℝ) × (Fin n → ℝ) =>
            (w.1, ρ p • w.1 + sC (ρ p) • w.2)) :=
          measurable_fst.prodMk (BstLean.Part105.meas_comb (ρ p) (sC (ρ p)))
        have e1 : ∫ ξ, F (p.1, ξ) * F (p.2, ξ) ∂stdGauss (Fin n × Fin m) =
            ∫ w, g w.1 * g (ρ p • w.1 + sC (ρ p) • w.2)
              ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) := by
          calc ∫ ξ, F (p.1, ξ) * F (p.2, ξ) ∂stdGauss (Fin n × Fin m)
              = ∫ q, g q.1 * g q.2 ∂(stdGauss (Fin n × Fin m)).map
                  (fun ξ => ((rowMat n (e p.1)).mulVec ξ, (rowMat n (e p.2)).mulVec ξ)) :=
                (integral_map hm.aemeasurable bG.meas.aestronglyMeasurable).symm
            _ = _ := by
                rw [pair_law h1 h2]
                exact integral_map hψ.aemeasurable bG.meas.aestronglyMeasurable
        have key := mehler2_sharp hρ1 hg hg
        have hle := (abs_le.mp key).2
        have hsq : Real.sqrt (V - S) * Real.sqrt (V - S) = V - S :=
          Real.mul_self_sqrt (by linarith)
        have e3 : ∑ i, (∫ z, g z * z i ∂stdGauss (Fin n)) * (∫ z, g z * z i ∂stdGauss (Fin n))
            = S := Finset.sum_congr rfl fun i _ => (sq _).symm
        rw [e3, mul_assoc, hsq] at hle
        have r1 : ∫ ξ, F (p.1, ξ) ∂stdGauss (Fin n × Fin m) = mg := row_mean h1 hg
        have r2 : ∫ ξ, F (p.2, ξ) ∂stdGauss (Fin n × Fin m) = mg := row_mean h2 hg
        simp only [hK, hJ]
        rw [e1, r1, r2]
        linarith [hle]
      · have hc : ∀ ξ, F (p.2, ξ) = g 0 := by
          intro ξ
          simp only [hFdef]
          rw [h2, rowMat_zero_mulVec]
        rw [hJ0 (hzero p.2 p.1 h2).2]
        simp only [hK, hc]
        rw [integral_mul_const, integral_const]
        simp
    · have hc : ∀ ξ, F (p.1, ξ) = g 0 := by
        intro ξ
        simp only [hFdef]
        rw [h1, rowMat_zero_mulVec]
      rw [hJ0 (hzero p.1 p.2 h1).1]
      simp only [hK, hc]
      rw [integral_const_mul, integral_const]
      simp
  -- the mean of the kernel `ρ`
  set T : ℝ := ∑ j, (∫ u, e u j ∂μ) ^ 2 with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hρint : ∫ p, ρ p ∂(μ.prod μ) = T := by
    rw [integral_prod _ (bρ.integrable _)]
    have h := kernel_sum μ be (BM.const (α := U) 1) (BM.const (α := U) 1)
    simp only [one_mul, mul_one] at h
    simp only [hρ]
    rw [h]
    exact Finset.sum_congr rfl fun j _ => (sq _).symm
  set R : ℝ := ∫ p, ρ p ^ 2 ∂(μ.prod μ) with hR
  have hR0 : 0 ≤ R := integral_nonneg fun p => sq_nonneg _
  have hJint : ∫ p, J p ∂(μ.prod μ) = T * S + R * (V - S) := by
    simp only [hJ]
    rw [integral_add ((bρ.mul (BM.const S)).integrable _)
      ((bρ.sq.mul (BM.const (V - S))).integrable _), integral_mul_const, integral_mul_const,
      hρint]
  have hvd := var_double μ (stdGauss (Fin n × Fin m)) bF
  have step1 : ∫ p, K p ∂(μ.prod μ) ≤ ∫ p, J p ∂(μ.prod μ) :=
    integral_mono (bK.integrable _) (bJ.integrable _) hpt
  have hfin : T * S + R * (V - S) ≤ (T + R) * V := by nlinarith
  calc _ = ∫ p, K p ∂(μ.prod μ) := hvd
    _ ≤ T * S + R * (V - S) := step1.trans hJint.le
    _ ≤ (T + R) * V := hfin

end varconst

end BstLean.Part149

open BstLean.Part149 in
#print axioms var_const
open BstLean.Part149 in
#print axioms mean_const
