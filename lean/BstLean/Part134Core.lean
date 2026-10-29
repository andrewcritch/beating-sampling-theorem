import BstLean.Part134Frame

/-!
# Part 134, item 3, the core: the variance of a mean over a Gaussian field

`var_core`: `G` a standard Gaussian `n × m` matrix (entries `ξ (i, j)`), `e_u ∈ ℝ^m` a
measurable family of vectors, each a unit vector or zero, with `E_u ⟨e_u, w⟩² ≤ L|w|²` for every
`w`; `f_u` a bounded jointly measurable family of functions on `ℝⁿ`. Then

`Var_G(E_u f_u(G e_u)) ≤ L · E_u Var_γ(f_u)`.

Proof (the Hermite route of the paper, with the expansion replaced by the sharp second-order
Gebelein inequality `mehler2_sharp`): the variance is
`E_{u,u'} Cov(f_u(G e_u), f_{u'}(G e_{u'}))`;
the pair `(G e_u, G e_{u'})` has correlation `ρ = ⟨e_u, e_{u'}⟩` (`pair_law`), so the covariance
is at most `ρ ⟨c_u, c_{u'}⟩ + ρ² a_u a_{u'}` (`c_u` the first chaos of `f_u`,
`a_u² = Var f_u − |c_u|²`).
The kernel `ρ` gives `|E_u c_u ⊗ e_u|² ≤ L E_u |c_u|²` (`frame_bound`); the kernel `ρ²` gives
`|E_u a_u e_u ⊗ e_u|² ≤ L E_u a_u²` (`frame_tensor`: the tensor comparison).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part134

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105 (BM sC)
open BstLean.Part112 (chaos1Bessel)
open BstLean.Part130

variable {n m : ℕ} {U : Type*} [MeasurableSpace U]

lemma rowMat_mulVec' (e : Fin m → ℝ) (ξ : Fin n × Fin m → ℝ) :
    (rowMat n e).mulVec ξ = (unflat ξ).mulVec e := rowMat_mulVec e (unflat ξ)

lemma rowMat_zero_mulVec (ξ : Fin n × Fin m → ℝ) :
    (rowMat n (0 : Fin m → ℝ)).mulVec ξ = 0 := by
  rw [rowMat_mulVec', Matrix.mulVec_zero]

section core

variable (μ : Measure U) [IsProbabilityMeasure μ]

/-- **The variance of a mean as a double integral of covariances.** -/
lemma var_double {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : U × Ω → ℝ} (hF : BM F) :
    ∫ ω, (∫ u, F (u, ω) ∂μ) ^ 2 ∂P - (∫ ω, (∫ u, F (u, ω) ∂μ) ∂P) ^ 2 =
      ∫ p, ((∫ ω, F (p.1, ω) * F (p.2, ω) ∂P) -
        (∫ ω, F (p.1, ω) ∂P) * (∫ ω, F (p.2, ω) ∂P)) ∂(μ.prod μ) := by
  have bA : BM (fun u => ∫ ω, F (u, ω) ∂P) := hF.integral_right P
  have bH : BM (fun q : (U × U) × Ω => F (q.1.1, q.2) * F (q.1.2, q.2)) :=
    (hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hF.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have bB : BM (fun p : U × U => ∫ ω, F (p.1, ω) * F (p.2, ω) ∂P) := bH.integral_right P
  have bAA : BM (fun p : U × U => (∫ ω, F (p.1, ω) ∂P) * (∫ ω, F (p.2, ω) ∂P)) :=
    (bA.comp measurable_fst).mul (bA.comp measurable_snd)
  rw [integral_sub (bB.integrable _) (bAA.integrable _)]
  congr 1
  · -- the second moment
    have e1 : ∀ ω, (∫ u, F (u, ω) ∂μ) ^ 2 =
        ∫ p, F (p.1, ω) * F (p.2, ω) ∂(μ.prod μ) := by
      intro ω
      have bω : BM (fun p : U × U => F (p.1, ω) * F (p.2, ω)) :=
        bH.comp (measurable_id.prodMk measurable_const)
      rw [integral_prod _ (bω.integrable _)]
      simp_rw [integral_const_mul, integral_mul_const]
      rw [sq]
    simp_rw [e1]
    exact integral_integral_swap (f := fun ω (p : U × U) => F (p.1, ω) * F (p.2, ω))
      ((bH.comp measurable_swap).integrable (P.prod (μ.prod μ)))
  · -- the square of the mean
    have e2 : ∫ ω, (∫ u, F (u, ω) ∂μ) ∂P = ∫ u, (∫ ω, F (u, ω) ∂P) ∂μ :=
      integral_integral_swap (f := fun ω u => F (u, ω))
        ((hF.comp measurable_swap).integrable (P.prod μ))
    rw [e2, integral_prod _ (bAA.integrable _)]
    simp_rw [integral_const_mul, integral_mul_const]
    rw [sq]

/-- **The core of Theorem S1 (c).** See the header of this file. -/
theorem var_core {e : U → Fin m → ℝ} (hem : Measurable e)
    (he : ∀ u, normSq (e u) = 1 ∨ e u = 0)
    {f : U × (Fin n → ℝ) → ℝ} (hf : BM f)
    {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, e u j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) :
    ∫ ξ, (∫ u, f (u, (rowMat n (e u)).mulVec ξ) ∂μ) ^ 2 ∂stdGauss (Fin n × Fin m) -
        (∫ ξ, (∫ u, f (u, (rowMat n (e u)).mulVec ξ) ∂μ) ∂stdGauss (Fin n × Fin m)) ^ 2 ≤
      L * ∫ u, (∫ z, (f (u, z) - ∫ y, f (u, y) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n)) ∂μ := by
  classical
  -- the field
  set F : U × (Fin n × Fin m → ℝ) → ℝ := fun q => f (q.1, (rowMat n (e q.1)).mulVec q.2) with hFdef
  have mZ : Measurable (fun q : U × (Fin n × Fin m → ℝ) => (rowMat n (e q.1)).mulVec q.2) := by
    simp_rw [rowMat_mulVec']
    exact measurable_mulVec_joint.comp
      ((measurable_unflat.comp measurable_snd).prodMk (hem.comp measurable_fst))
  have bF : BM F := hf.comp (measurable_fst.prodMk mZ)
  -- the entries of `e` are bounded
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
  -- the statistics of `f_u`
  have bfu : ∀ u, BM (fun z => f (u, z)) := fun u => hf.comp measurable_prodMk_left
  set mm : U → ℝ := fun u => ∫ y, f (u, y) ∂stdGauss (Fin n) with hmm
  have bmm : BM mm := hf.integral_right _
  set V : U → ℝ := fun u => ∫ z, (f (u, z) - mm u) ^ 2 ∂stdGauss (Fin n) with hV
  have bV : BM V := ((hf.sub (bmm.comp measurable_fst)).sq).integral_right _
  set cf : U → Fin n → ℝ := fun u i => ∫ z, f (u, z) * z i ∂stdGauss (Fin n) with hcf
  have hbes : ∀ u, ∑ i, cf u i ^ 2 ≤ V u := fun u => chaos1Bessel (Fin n) _ (bfu u)
  obtain ⟨CV, hCV⟩ := bV.bdd
  have hV0 : ∀ u, 0 ≤ V u := fun u => integral_nonneg fun z => sq_nonneg _
  have bcf : ∀ i, BM (fun u => cf u i) := by
    intro i
    refine ⟨((hf.meas.mul ((measurable_pi_apply i).comp
      measurable_snd)).stronglyMeasurable.integral_prod_right').measurable, Real.sqrt CV,
      fun u => Real.abs_le_sqrt ?_⟩
    have h1 : cf u i ^ 2 ≤ ∑ i, cf u i ^ 2 :=
      Finset.single_le_sum (f := fun i => cf u i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
    exact h1.trans ((hbes u).trans ((le_abs_self _).trans (hCV u)))
  set a : U → ℝ := fun u => Real.sqrt (V u - ∑ i, cf u i ^ 2) with ha
  have ha2 : ∀ u, a u ^ 2 = V u - ∑ i, cf u i ^ 2 := fun u =>
    Real.sq_sqrt (by linarith [hbes u])
  have ba : BM a := by
    refine ⟨(bV.meas.sub (Finset.measurable_sum _ fun i _ => (bcf i).meas.pow_const 2)).sqrt,
      Real.sqrt CV, fun u => ?_⟩
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    have : 0 ≤ ∑ i, cf u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith [(le_abs_self (V u)).trans (hCV u)]
  -- the kernels
  set ρ : U × U → ℝ := fun p => ∑ j, e p.1 j * e p.2 j with hρ
  set ξ₂ : U → Fin m × Fin m → ℝ := fun u q => e u q.1 * e u q.2 with hξ₂
  have bξ₂ : ∀ q, BM (fun u => ξ₂ u q) := fun q => (be q.1).mul (be q.2)
  have hρ2 : ∀ p : U × U, ρ p ^ 2 = ∑ q, ξ₂ p.1 q * ξ₂ p.2 q := by
    intro p
    simp only [hρ, hξ₂]
    rw [sq, Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  set J₂ : U × U → ℝ := fun p =>
    (∑ i, (∑ j, e p.1 j * e p.2 j) * (cf p.1 i * cf p.2 i)) +
      (∑ q, ξ₂ p.1 q * ξ₂ p.2 q) * (a p.1 * a p.2) with hJ₂
  have bker : BM (fun p : U × U => ∑ j, e p.1 j * e p.2 j) :=
    bm_sum Finset.univ fun j _ => ((be j).comp measurable_fst).mul ((be j).comp measurable_snd)
  have bker2 : BM (fun p : U × U => ∑ q, ξ₂ p.1 q * ξ₂ p.2 q) :=
    bm_sum Finset.univ fun q _ => ((bξ₂ q).comp measurable_fst).mul ((bξ₂ q).comp measurable_snd)
  have bJi : ∀ i, BM (fun p : U × U => (∑ j, e p.1 j * e p.2 j) * (cf p.1 i * cf p.2 i)) :=
    fun i => bker.mul (((bcf i).comp measurable_fst).mul ((bcf i).comp measurable_snd))
  have bJa : BM (fun p : U × U => (∑ q, ξ₂ p.1 q * ξ₂ p.2 q) * (a p.1 * a p.2)) :=
    bker2.mul ((ba.comp measurable_fst).mul (ba.comp measurable_snd))
  have bJ₂ : BM J₂ := (bm_sum Finset.univ fun i _ => bJi i).add bJa
  -- the covariance kernel
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
  -- the pointwise bound
  have hrow : ∀ u, normSq (e u) = 1 →
      ∫ ξ, F (u, ξ) ∂stdGauss (Fin n × Fin m) = mm u := by
    intro u h1
    have hm : Measurable (fun ξ : Fin n × Fin m → ℝ => (rowMat n (e u)).mulVec ξ) :=
      measurable_mulVec_left _
    calc ∫ ξ, F (u, ξ) ∂stdGauss (Fin n × Fin m)
        = ∫ z, f (u, z) ∂(stdGauss (Fin n × Fin m)).map (fun ξ => (rowMat n (e u)).mulVec ξ) :=
          (integral_map hm.aemeasurable (bfu u).meas.aestronglyMeasurable).symm
      _ = mm u := by rw [row_law h1]
  have hpt : ∀ p, K p ≤ J₂ p := by
    intro p
    have hzero : ∀ u u' : U, e u = 0 → ρ (u, u') = 0 ∧ ρ (u', u) = 0 := by
      intro u u' h
      simp [hρ, h]
    have hJ0 : ρ p = 0 → J₂ p = 0 := by
      intro h0
      have h0' : ∑ j, e p.1 j * e p.2 j = 0 := h0
      have h2 := hρ2 p
      rw [h0] at h2
      simp only [hJ₂, h0', ← h2]
      simp
    rcases he p.1 with h1 | h1
    · rcases he p.2 with h2 | h2
      · -- both unit vectors
        have hρ1 := abs_dot_le_one h1 h2
        have hm : Measurable (fun ξ : Fin n × Fin m → ℝ =>
            ((rowMat n (e p.1)).mulVec ξ, (rowMat n (e p.2)).mulVec ξ)) :=
          (measurable_mulVec_left _).prodMk (measurable_mulVec_left _)
        have bG : BM (fun q : (Fin n → ℝ) × (Fin n → ℝ) => f (p.1, q.1) * f (p.2, q.2)) :=
          ((bfu p.1).comp measurable_fst).mul ((bfu p.2).comp measurable_snd)
        have hψ : Measurable (fun w : (Fin n → ℝ) × (Fin n → ℝ) =>
            (w.1, ρ p • w.1 + sC (ρ p) • w.2)) :=
          measurable_fst.prodMk (BstLean.Part105.meas_comb (ρ p) (sC (ρ p)))
        have e1 : ∫ ξ, F (p.1, ξ) * F (p.2, ξ) ∂stdGauss (Fin n × Fin m) =
            ∫ w, f (p.1, w.1) * f (p.2, ρ p • w.1 + sC (ρ p) • w.2)
              ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) := by
          calc ∫ ξ, F (p.1, ξ) * F (p.2, ξ) ∂stdGauss (Fin n × Fin m)
              = ∫ q, f (p.1, q.1) * f (p.2, q.2) ∂(stdGauss (Fin n × Fin m)).map
                  (fun ξ => ((rowMat n (e p.1)).mulVec ξ, (rowMat n (e p.2)).mulVec ξ)) :=
                (integral_map hm.aemeasurable bG.meas.aestronglyMeasurable).symm
            _ = _ := by
                rw [pair_law h1 h2]
                exact integral_map hψ.aemeasurable bG.meas.aestronglyMeasurable
        have key := mehler2_sharp hρ1 (bfu p.1) (bfu p.2)
        have hle := (abs_le.mp key).2
        simp only [hK, hJ₂]
        rw [e1, hrow p.1 h1, hrow p.2 h2, ← hρ2 p]
        have e3 : ∑ i, (∑ j, e p.1 j * e p.2 j) * (cf p.1 i * cf p.2 i) =
            ρ p * ∑ i, cf p.1 i * cf p.2 i := by
          rw [Finset.mul_sum]
        rw [e3]
        linarith [hle]
      · -- `e p.2 = 0`
        have hc : ∀ ξ, F (p.2, ξ) = f (p.2, 0) := by
          intro ξ
          simp only [hFdef]
          rw [h2, rowMat_zero_mulVec]
        rw [hJ0 (hzero p.2 p.1 h2).2]
        simp only [hK, hc]
        rw [integral_mul_const, integral_const]
        simp
    · -- `e p.1 = 0`
      have hc : ∀ ξ, F (p.1, ξ) = f (p.1, 0) := by
        intro ξ
        simp only [hFdef]
        rw [h1, rowMat_zero_mulVec]
      rw [hJ0 (hzero p.1 p.2 h1).1]
      simp only [hK, hc]
      rw [integral_const_mul, integral_const]
      simp
  -- assemble
  have hvd := var_double μ (stdGauss (Fin n × Fin m)) bF
  rw [hvd]
  have step1 : ∫ p, K p ∂(μ.prod μ) ≤ ∫ p, J₂ p ∂(μ.prod μ) :=
    integral_mono (bK.integrable _) (bJ₂.integrable _) hpt
  have step2 : ∫ p, J₂ p ∂(μ.prod μ) =
      (∑ i, ∑ j, (∫ u, cf u i * e u j ∂μ) ^ 2) + ∑ q, (∫ u, a u * ξ₂ u q ∂μ) ^ 2 := by
    simp only [hJ₂]
    rw [integral_add ((bm_sum Finset.univ fun i _ => bJi i).integrable _) (bJa.integrable _),
      integral_finsetSum _ fun i _ => (bJi i).integrable _]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_prod _ ((bJi i).integrable _)]
      rw [kernel_sum μ be (bcf i) (bcf i)]
      exact Finset.sum_congr rfl fun j _ => (sq _).symm
    · rw [integral_prod _ (bJa.integrable _)]
      rw [kernel_sum μ bξ₂ ba ba]
      exact Finset.sum_congr rfl fun q _ => (sq _).symm
  have step3 : ∀ i, ∑ j, (∫ u, cf u i * e u j ∂μ) ^ 2 ≤ L * ∫ u, cf u i ^ 2 ∂μ :=
    fun i => frame_bound μ be (bcf i) hL0 hL
  have step4 : ∑ q, (∫ u, a u * ξ₂ u q ∂μ) ^ 2 ≤ L * ∫ u, a u ^ 2 ∂μ :=
    frame_bound μ bξ₂ ba hL0 (frame_tensor μ be hn1 hL)
  have step5 : (∑ i, ∫ u, cf u i ^ 2 ∂μ) + ∫ u, a u ^ 2 ∂μ = ∫ u, V u ∂μ := by
    rw [← integral_finsetSum _ fun i _ => (bcf i).sq.integrable μ,
      ← integral_add ((bm_sum Finset.univ fun i _ => (bcf i).sq).integrable μ) (ba.sq.integrable μ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [ha2 u]
    ring
  calc ∫ p, K p ∂(μ.prod μ) ≤ ∫ p, J₂ p ∂(μ.prod μ) := step1
    _ = (∑ i, ∑ j, (∫ u, cf u i * e u j ∂μ) ^ 2) + ∑ q, (∫ u, a u * ξ₂ u q ∂μ) ^ 2 := step2
    _ ≤ (∑ i, L * ∫ u, cf u i ^ 2 ∂μ) + L * ∫ u, a u ^ 2 ∂μ :=
        add_le_add (Finset.sum_le_sum fun i _ => step3 i) step4
    _ = L * ∫ u, V u ∂μ := by rw [← step5, ← Finset.mul_sum]; ring

end core

end BstLean.Part134

open BstLean.Part134 in
#print axioms var_core
