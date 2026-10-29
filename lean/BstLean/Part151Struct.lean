import BstLean.Part151Gauss
import BstLean.Part150Thm

/-!
# Part 151, item 1: the structure of the error (Lemma ST (a) of the document)

Role: `delegations/statements/p151-spec.md`, item 1. Paper source:
`proofs/option-n/theorem5-04-standin-structure.tex`, Lemma ST (a).

Notation. `W` (World network), `A` (Agent network), `F = (F₁, F₂, F₃)`; `F₃` has one row, the
last row `f₃` of `F`. `bh : CMap n` is ANY centre map: a function of `(W, A₁, A₂)` with values in
`ℝ^{m_A}`. The estimator with `k` forward passes of `F` is `gSampH bh k W A F η`
(Part 150): `(1/k)·Σ_j F(A₃·b + σ_p·η_j)`, `b = bh(W, A₁, A₂)`, `σ_p = tauOutOf n b
= √max(0, 2/n − (2/m_A)|b|²)`. The population mean over the stand-in input is
`B′ = gA W A F = E_{x∼ν′} F(A(x))`, `ν′ = cheapIn (cenA W) (tauWA W)` (Part 141).

* `Fix k n`: the type of the variables that are fixed in the last step: `((W, A, (F₁, F₂)), η)`.
  `fixP k n`: their distribution. `Row n`: the type of the last row; `rowP n` its distribution.
  `Joint k n`: the type of `((W, A, F), η)`. `restJ`, `rowJ`: the two projections.
* `joint_map`: under `mlpTriple 2 n ⊗ gamK k n` the pair `(restJ, rowJ)` has the distribution
  `fixP k n ⊗ rowP n`.
* `dHat bh k ω`: the feature error `Δ̂′ = (1/k)Σ_j z_F(c_A + σ_pη_j) − E_{x∼ν′} z_F(A(x))`, a
  vector of `ℝ^{m_F}`; a function of `ω : Fix k n` only (it does not depend on `f₃`).
* **`struct151`**: `g − B′ = f₃·Δ̂′`.
* `row_gauss`: `f₃·Δ` is centred Gaussian with variance `t_F·|Δ|²`.
* `measurable_dHat`, `measurable_linJ`: measurability.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss continuous_hid2_joint)
open BstLean.Part138 (cheapIn integral_cheapIn)
open BstLean.Part139 (gamK)
open BstLean.Part141 (cenA tauWA gA measurable_cenA measurable_tauWA)
open BstLean.Part149 (evF thA tauOutOf)
open BstLean.Part150 (CMap gSampH preH measurable_preH)

/-! ## Three facts about product measures -/

section prodfacts

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

lemma assoc_symm_map (a : Measure α) (b : Measure β) (c : Measure γ) [SFinite a] [SFinite b]
    [SFinite c] :
    (a.prod (b.prod c)).map (fun p : α × β × γ => ((p.1, p.2.1), p.2.2)) = (a.prod b).prod c := by
  have h := Measure.prodAssoc_prod (μ := a) (ν := b) (τ := c)
  rw [← h, Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable]
  have e : ((fun p : α × β × γ => ((p.1, p.2.1), p.2.2)) ∘ MeasurableEquiv.prodAssoc) = id := by
    funext p; rfl
  rw [e, Measure.map_id]

lemma map_snd_prod {β' : Type*} [MeasurableSpace β'] (a : Measure α) [SFinite a] {b : Measure β}
    [SFinite b] {b' : Measure β'} {f : β → β'} (hf : Measurable f) (h : b.map f = b') :
    (a.prod b).map (fun p : α × β => (p.1, f p.2)) = a.prod b' := by
  have h1 := Measure.map_prod_map a b (f := id) (g := f) measurable_id hf
  rw [Measure.map_id, h] at h1
  rw [h1]
  rfl

lemma map_fst_prod {α' : Type*} [MeasurableSpace α'] {a : Measure α} [SFinite a] (b : Measure β)
    [SFinite b] {a' : Measure α'} {f : α → α'} (hf : Measurable f) (h : a.map f = a') :
    (a.prod b).map (fun p : α × β => (f p.1, p.2)) = a'.prod b := by
  have h1 := Measure.map_prod_map a b (f := f) (g := id) hf measurable_id
  rw [Measure.map_id, h] at h1
  rw [h1]
  rfl

lemma swap_last (a : Measure α) (b : Measure β) (c : Measure γ) [SFinite a] [SFinite b]
    [SFinite c] :
    ((a.prod b).prod c).map (fun p : (α × β) × γ => ((p.1.1, p.2), p.1.2)) = (a.prod c).prod b := by
  have h1 := Measure.prodAssoc_prod (μ := a) (ν := b) (τ := c)
  have h2 : (a.prod (b.prod c)).map (fun p : α × β × γ => (p.1, Prod.swap p.2)) =
      a.prod (c.prod b) := map_snd_prod a measurable_swap Measure.prod_swap
  have h3 := assoc_symm_map a c b
  rw [← h2, ← h1, Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map (by fun_prop) (by fun_prop)] at h3
  rw [← h3]
  rfl

end prodfacts

/-! ## The spaces -/

/-- The variables that are fixed in the last step: `((W, A, (F₁, F₂)), η)`. -/
abbrev Fix (k n : ℕ) : Type :=
  (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × HidParam n (mF n)) × (Fin k → Fin n → ℝ)

/-- The last matrix of `F`: one row, the vector `f₃`. -/
abbrev Row (n : ℕ) : Type := Matrix (Fin 1) (Fin (mF n)) ℝ

/-- All variables: `((W, A, F), η)`. -/
abbrev Joint (k n : ℕ) : Type :=
  (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ)

/-- The distribution of `((W, A, (F₁, F₂)), η)`. -/
noncomputable def fixP (k n : ℕ) : Measure (Fix k n) :=
  ((mlpGauss (2 * n) (mW n) n).prod ((mlpGauss n (mA n) n).prod (hidGauss n (mF n)))).prod
    (gamK k n)

instance (k n : ℕ) : IsProbabilityMeasure (fixP k n) := by unfold fixP; infer_instance

/-- The distribution of the last row of `F`: independent `N(0, t_F)` entries, `t_F = 2/m_F`. -/
noncomputable def rowP (n : ℕ) : Measure (Row n) := gaussMat 1 (mF n) (2 / (mF n : ℝ))

instance (n : ℕ) : IsProbabilityMeasure (rowP n) := by unfold rowP; infer_instance

/-- The joint distribution of `((W, A, F), η)`. -/
noncomputable def jointP (k n : ℕ) : Measure (Joint k n) := (mlpTriple 2 n).prod (gamK k n)

instance (k n : ℕ) : IsProbabilityMeasure (jointP k n) := by unfold jointP; infer_instance

variable {k n : ℕ}

/-- All variables except the last row of `F`. -/
def restJ (p : Joint k n) : Fix k n := ((p.1.1, p.1.2.1, (p.1.2.2.1, p.1.2.2.2.1)), p.2)

/-- The last row of `F`. -/
def rowJ (p : Joint k n) : Row n := p.1.2.2.2.2

/-- Put the last row back. -/
def joinJ (ω : Fix k n) (w : Row n) : Joint k n :=
  ((ω.1.1, ω.1.2.1, (ω.1.2.2.1, ω.1.2.2.2, w)), ω.2)

@[simp] lemma joinJ_rest_row (p : Joint k n) : joinJ (restJ p) (rowJ p) = p := rfl

@[simp] lemma restJ_joinJ (ω : Fix k n) (w : Row n) : restJ (joinJ ω w) = ω := rfl

@[simp] lemma rowJ_joinJ (ω : Fix k n) (w : Row n) : rowJ (joinJ ω w) = w := rfl

lemma measurable_restJ : Measurable (restJ (k := k) (n := n)) := by
  unfold restJ; fun_prop

lemma measurable_rowJ : Measurable (rowJ (k := k) (n := n)) := by
  unfold rowJ; fun_prop

lemma measurable_joinJ : Measurable (fun q : Fix k n × Row n => joinJ q.1 q.2) := by
  unfold joinJ; fun_prop

/-- **The last row of `F` is independent of all other variables**: under the joint distribution
of `((W, A, F), η)`, the pair (all other variables, last row) has the product distribution. -/
theorem joint_map :
    (jointP k n).map (fun p => (restJ p, rowJ p)) = (fixP k n).prod (rowP n) := by
  -- `F = (F₁, (F₂, F₃))` to `((F₁, F₂), F₃)`
  have s1 : (mlpGauss n (mF n) 1).map
      (fun F : MlpParam n (mF n) 1 => (((F.1, F.2.1) : HidParam n (mF n)), F.2.2)) =
      (hidGauss n (mF n)).prod (rowP n) := by
    unfold mlpGauss hidGauss rowP
    exact assoc_symm_map _ _ _
  -- `(A, F)` to `((A, (F₁, F₂)), F₃)`
  have s2 : ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)).map
      (fun q : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
        ((q.1, ((q.2.1, q.2.2.1) : HidParam n (mF n))), q.2.2.2)) =
      ((mlpGauss n (mA n) n).prod (hidGauss n (mF n))).prod (rowP n) := by
    have h := map_snd_prod (mlpGauss n (mA n) n) (by fun_prop) s1
    have h2 := assoc_symm_map (mlpGauss n (mA n) n) (hidGauss n (mF n)) (rowP n)
    rw [← h, Measure.map_map (by fun_prop) (by fun_prop)] at h2
    rw [← h2]
    rfl
  -- `(W, (A, F))` to `((W, (A, (F₁, F₂))), F₃)`
  have s3 : (mlpTriple 2 n).map
      (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
        ((t.1, t.2.1, ((t.2.2.1, t.2.2.2.1) : HidParam n (mF n))), t.2.2.2.2)) =
      ((mlpGauss (2 * n) (mW n) n).prod
        ((mlpGauss n (mA n) n).prod (hidGauss n (mF n)))).prod (rowP n) := by
    have h := map_snd_prod (mlpGauss (2 * n) (mW n) n) (by fun_prop) s2
    have h2 := assoc_symm_map (mlpGauss (2 * n) (mW n) n)
      ((mlpGauss n (mA n) n).prod (hidGauss n (mF n))) (rowP n)
    rw [← h, Measure.map_map (by fun_prop) (by fun_prop)] at h2
    rw [← h2]
    rfl
  -- with `η`
  have s4 := map_fst_prod (gamK k n) (by fun_prop) s3
  have s5 := swap_last ((mlpGauss (2 * n) (mW n) n).prod
    ((mlpGauss n (mA n) n).prod (hidGauss n (mF n)))) (rowP n) (gamK k n)
  rw [← s4, Measure.map_map (by fun_prop) (by fun_prop)] at s5
  unfold fixP jointP
  rw [← s5]
  rfl

/-! ## The feature error -/

/-- **The feature error** `Δ̂′ = (1/k)·Σ_j z_F(c_A + σ_p·η_j) − E_{x∼ν′} z_F(A(x))`, for the
centre map `bh`; `z_F(y) = ReLU(F₂·ReLU(F₁y))` (`hid2`). A vector of `ℝ^{m_F}`; a function of
`((W, A, (F₁, F₂)), η)`. -/
noncomputable def dHat (bh : CMap n) (k : ℕ) (ω : Fix k n) : Fin (mF n) → ℝ := fun i =>
  (k : ℝ)⁻¹ * ∑ j, hid2 ω.1.2.2.1 ω.1.2.2.2 (preH bh ω.1.1 ω.1.2.1 (ω.2 j)) i -
    ∫ x, hidF ω.1.2.2.1 ω.1.2.2.2 ω.1.2.1 x i ∂cheapIn (cenA ω.1.1) (tauWA ω.1.1)

/-- The conditional variance of the error given all but the last row: `V′ = t_F·|Δ̂′|²`. -/
noncomputable def vHat (bh : CMap n) (k : ℕ) (ω : Fix k n) : ℝ :=
  2 / (mF n : ℝ) * normSq (dHat bh k ω)

lemma vHat_nonneg (bh : CMap n) (k : ℕ) (ω : Fix k n) : 0 ≤ vHat bh k ω := by
  unfold vHat
  have : 0 ≤ normSq (dHat bh k ω) := Finset.sum_nonneg fun i _ => sq_nonneg _
  positivity

/-- The linear form `f₃·Δ̂′`. -/
noncomputable def linJ (bh : CMap n) (k : ℕ) (ω : Fix k n) (w : Row n) : ℝ :=
  rowOf 0 w ⬝ᵥ dHat bh k ω

lemma hidF_cheap_integrable (hn : 1 ≤ n) {mA' mF' : ℕ} (F₁ : Matrix (Fin mF') (Fin n) ℝ)
    (F₂ : Matrix (Fin mF') (Fin mF') ℝ) (A : MlpParam n mA' n) (c : Fin n → ℝ) (τ : ℝ)
    (i : Fin mF') : Integrable (fun x => hidF F₁ F₂ A x i) (cheapIn c τ) := by
  have hc := continuous_hidF F₁ F₂ A i
  obtain ⟨C, hC⟩ := isCompact_unit.exists_bound_of_continuousOn hc.continuousOn
  unfold cheapIn
  have hm : Measurable (fun γ : Fin n → ℝ => sphPt (c + τ • γ)) :=
    measurable_sphPt.comp (measurable_const.add (measurable_const_smul τ))
  rw [integrable_map_measure hc.measurable.aestronglyMeasurable hm.aemeasurable]
  refine Integrable.of_bound (hc.measurable.comp hm).aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall fun γ => hC _ (normSq_sphPt hn _)

/-- **Lemma ST (a): the structure of the error.** For every centre map `bh`, every `k ≥ 1` and
every value of the variables: `g − B′ = f₃·Δ̂′`, where `g = gSampH bh k W A F η` is the mean of
the `k` values `F(c_A + σ_pη_j)`, and `B′ = gA W A F = E_{x∼ν′} F(A(x))`. -/
theorem struct151 (hn : 1 ≤ n) (bh : CMap n) (p : Joint k n) :
    gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gA p.1.1 p.1.2.1 p.1.2.2 =
      linJ bh k (restJ p) (rowJ p) := by
  obtain ⟨⟨W, A, F₁, F₂, F₃⟩, γ⟩ := p
  simp only [restJ, rowJ, linJ]
  have hg : gA W A (F₁, F₂, F₃) =
      ∑ l, F₃ 0 l * ∫ x, hidF F₁ F₂ A x l ∂cheapIn (cenA W) (tauWA W) := by
    unfold gA
    simp_rw [phiN_last]
    rw [integral_finsetSum _ fun l _ =>
      (hidF_cheap_integrable hn F₁ F₂ A (cenA W) (tauWA W) l).const_mul _]
    simp_rw [integral_const_mul]
  have hs : gSampH bh k W A (F₁, F₂, F₃) γ =
      ∑ l, F₃ 0 l * ((k : ℝ)⁻¹ * ∑ j, hid2 F₁ F₂ (preH bh W A (γ j)) l) := by
    unfold gSampH
    have e : ∀ y : Fin n → ℝ, evF (F₁, F₂, F₃) y = ∑ l, F₃ 0 l * hid2 F₁ F₂ y l := fun y => rfl
    simp_rw [e]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_sum]
    ring
  rw [hg, hs, ← Finset.sum_sub_distrib]
  simp only [dotProduct, rowOf, dHat]
  exact Finset.sum_congr rfl fun l _ => by ring

/-! ## The distribution of the linear form -/

/-- **A linear form of the last row is centred Gaussian**: for a one-row matrix `M` with
independent `N(0, v)` entries and a vector `Δ`, `M·Δ ∼ N(0, v·|Δ|²)`. -/
theorem row_gauss {m : ℕ} {v : ℝ} (hv : 0 ≤ v) (Δ : Fin m → ℝ) :
    (gaussMat 1 m v).map (fun M => rowOf 0 M ⬝ᵥ Δ) = gaussianReal 0 (v * normSq Δ).toNNReal := by
  have hns : 0 ≤ normSq Δ := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h := gaussMat_mulVec (m := 1) v Δ
  have h1 := congrArg (Measure.map (fun y : Fin 1 → ℝ => y 0)) h
  rw [Measure.map_map (measurable_pi_apply 0) (by fun_prop),
    Measure.map_map (measurable_pi_apply 0) (by fun_prop)] at h1
  have e1 : ((fun y : Fin 1 → ℝ => y 0) ∘ fun M : Matrix (Fin 1) (Fin m) ℝ => M.mulVec Δ) =
      fun M => rowOf 0 M ⬝ᵥ Δ := by
    funext M; rfl
  have e2 : ((fun y : Fin 1 → ℝ => y 0) ∘ fun ξ : Fin 1 → ℝ => (√v * √(normSq Δ)) • ξ) =
      (fun x : ℝ => (√v * √(normSq Δ)) * x) ∘ fun ξ : Fin 1 → ℝ => ξ 0 := by
    funext ξ; simp
  have h2 : (stdGauss (Fin 1)).map (fun ξ : Fin 1 → ℝ => ξ 0) = gaussianReal 0 1 :=
    (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0).map_eq
  have h3 : Measure.map ((fun x : ℝ => (√v * √(normSq Δ)) * x) ∘ fun ξ : Fin 1 → ℝ => ξ 0)
      (stdGauss (Fin 1)) = Measure.map (fun x : ℝ => (√v * √(normSq Δ)) * x)
        (Measure.map (fun ξ : Fin 1 → ℝ => ξ 0) (stdGauss (Fin 1))) :=
    (Measure.map_map (by fun_prop) (measurable_pi_apply 0)).symm
  rw [e1, e2, h3, h2, gaussianReal_map_const_mul] at h1
  rw [h1]
  congr 1
  · simp
  · ext
    simp only [mul_one, NNReal.coe_mk]
    rw [Real.coe_toNNReal _ (mul_nonneg hv hns), mul_pow, Real.sq_sqrt hv, Real.sq_sqrt hns]

/-- Given all other variables, `f₃·Δ̂′` is centred Gaussian with variance `V′ = t_F·|Δ̂′|²`. -/
theorem linJ_gauss (bh : CMap n) (k : ℕ) (ω : Fix k n) :
    (rowP n).map (linJ bh k ω) = gaussianReal 0 (vHat bh k ω).toNNReal := by
  unfold rowP linJ vHat
  exact row_gauss (by positivity) _

/-! ## Measurability -/

lemma measurable_dHat {bh : CMap n} (hbh : Measurable bh) (k : ℕ) (i : Fin (mF n)) :
    Measurable (fun ω : Fix k n => dHat bh k ω i) := by
  unfold dHat
  refine Measurable.sub (measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)) ?_
  · have hpre : Measurable (fun ω : Fix k n => preH bh ω.1.1 ω.1.2.1 (ω.2 j)) := by
      have h := (measurable_preH hbh).comp
        (f := fun ω : Fix k n => ((ω.1.1, ω.1.2.1), ω.2 j)) (by fun_prop)
      simpa only [Function.comp_def] using h
    have hF : Measurable (fun ω : Fix k n => (ω.1.2.2 : HidParam n (mF n))) := by fun_prop
    have h := ((continuous_apply i).comp continuous_hid2_joint).measurable.comp
      (hF.prodMk hpre)
    simpa only [Function.comp_def] using h
  · have hφ : ∀ ω : Fix k n, Measurable (fun x => hidF ω.1.2.2.1 ω.1.2.2.2 ω.1.2.1 x i) :=
      fun ω => (continuous_hidF _ _ _ i).measurable
    simp_rw [fun ω : Fix k n => integral_cheapIn (cenA ω.1.1) (tauWA ω.1.1) (hφ ω)]
    refine StronglyMeasurable.measurable ?_
    refine StronglyMeasurable.integral_prod_right'
      (f := fun q : Fix k n × (Fin n → ℝ) =>
        hidF q.1.1.2.2.1 q.1.1.2.2.2 q.1.1.2.1 (sphPt (cenA q.1.1.1 + tauWA q.1.1.1 • q.2)) i) ?_
    refine Measurable.stronglyMeasurable ?_
    have hx : Measurable (fun q : Fix k n × (Fin n → ℝ) =>
        sphPt (cenA q.1.1.1 + tauWA q.1.1.1 • q.2)) := by
      have hc : Measurable (fun q : Fix k n × (Fin n → ℝ) => cenA q.1.1.1) :=
        measurable_cenA.comp (by fun_prop)
      have ht : Measurable (fun q : Fix k n × (Fin n → ℝ) => tauWA q.1.1.1) :=
        measurable_tauWA.comp (by fun_prop)
      have hs : Measurable (fun q : Fix k n × (Fin n → ℝ) => q.2) := measurable_snd
      exact measurable_sphPt.comp (hc.add (ht.smul hs))
    have hA : Measurable (fun q : Fix k n × (Fin n → ℝ) => mlpEval q.1.1.2.1
        (sphPt (cenA q.1.1.1 + tauWA q.1.1.1 • q.2))) :=
      continuous_mlpEval_joint.measurable.comp
        (Measurable.prodMk (by fun_prop) hx)
    have hF : Measurable (fun q : Fix k n × (Fin n → ℝ) => (q.1.1.2.2 : HidParam n (mF n))) := by
      fun_prop
    have h := ((continuous_apply i).comp continuous_hid2_joint).measurable.comp (hF.prodMk hA)
    simpa only [Function.comp_def, hidF] using h

lemma measurable_vHat {bh : CMap n} (hbh : Measurable bh) (k : ℕ) :
    Measurable (fun ω : Fix k n => vHat bh k ω) := by
  unfold vHat normSq
  exact measurable_const.mul
    (Finset.measurable_sum _ fun i _ => (measurable_dHat hbh k i).pow_const 2)

lemma measurable_linJ {bh : CMap n} (hbh : Measurable bh) (k : ℕ) :
    Measurable (fun q : Fix k n × Row n => linJ bh k q.1 q.2) := by
  unfold linJ
  simp only [dotProduct, rowOf]
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_
  · fun_prop
  · exact (measurable_dHat hbh k i).comp measurable_fst

end BstLean.Part151
