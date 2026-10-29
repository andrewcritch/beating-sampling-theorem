import BstLean.Part183EnJ

/-!
# Part 184 (file `Row`): per-row moment lemmas for the row moment expansion of the energy

No proof is left open; no `native_decide` or `axiom` is used.

Generic row: `g_ν(v) = c v + √t·⟨ν, w v⟩` with `c`, `w` bounded measurable, `E_v w = 0`,
`E_v⟨e, w⟩² ≤ Λ|e|²`; `rowE ν = E_v ReLU(g_ν)²`, `rowV ν = Var_v ReLU(g_ν)`.

* `rowV_nonneg`, **`rowV_le_var`** (R3): `0 ≤ rowV ≤ Var_v g_ν`.
* **`row_var_mom`** (R4): `E_M (E_v((M(a v − ā))_j)²)^p ≤ E|g|^{2p}·t^p·(4K²)^{p−1}·E_v|a v − ā|²`
  for `M ∼ gaussMat m m t`, `|a v|² ≤ K²`.
* `row_local`, `sqrt_rowE_euLip`: the one-row local estimate and the Lipschitz bound of `√rowE`.
* `trunc_poinc_p`, `trunc_poinc_2`: truncated Gaussian Poincaré inequalities (order `2p` with
  Pisier's constant; order 2 sharp) from a local estimate.
* **`row_var_sharp`** (R1): `Var_ν rowE ≤ 4tΛ·E_ν rowV`.
* **`row_mom_p`** (R2): `E|rowE − E rowE|^{2p} ≤ (π/2)^{2p}·E|g|^{2p}·(4tΛ)^p·E rowV^p`.
* `rowE_pow_integrable`: every power of `rowE` is integrable.
-/

open MeasureTheory ProbabilityTheory Real Matrix Filter Topology
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part170
open BstLean.Part162 (gmom gmom_nonneg)
open BstLean.Part148 (EuLip)

namespace BstLean.Part184

section row
variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]

/-- The row argument `g_ν(v) = c v + √t·⟨ν, w v⟩`. -/
noncomputable def rowG (c : V → ℝ) (w : V → Fin m → ℝ) (t : ℝ) (ν : Fin m → ℝ) (v : V) : ℝ :=
  c v + √t * (ν ⬝ᵥ w v)

/-- The row energy `E_v ReLU(g_ν)²`. -/
noncomputable def rowE (μ : Measure V) (c : V → ℝ) (w : V → Fin m → ℝ) (t : ℝ)
    (ν : Fin m → ℝ) : ℝ :=
  ∫ v, relu (rowG c w t ν v) ^ 2 ∂μ

/-- The row variance `Var_v ReLU(g_ν)`. -/
noncomputable def rowV (μ : Measure V) (c : V → ℝ) (w : V → Fin m → ℝ) (t : ℝ)
    (ν : Fin m → ℝ) : ℝ :=
  ∫ v, relu (rowG c w t ν v) ^ 2 ∂μ - (∫ v, relu (rowG c w t ν v) ∂μ) ^ 2

/-- Integrability of a continuous function of the bounded pair `(c v, w v)`. -/
lemma int_pair {c : V → ℝ} {w : V → Fin m → ℝ} (hc : Measurable c) (hw : Measurable w)
    {Kc K : ℝ} (hcK : ∀ v, |c v| ≤ Kc) (hwK : ∀ v, ‖w v‖ ≤ K)
    {f : ℝ × (Fin m → ℝ) → ℝ} (hf : Continuous f) :
    Integrable (fun v => f (c v, w v)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall ((0 : ℝ × (Fin m → ℝ))) (max Kc K)).exists_bound_of_continuousOn
    hf.continuousOn
  refine Integrable.mono' (integrable_const C) (hf.measurable.comp
    (hc.prodMk hw)).aestronglyMeasurable (Filter.Eventually.of_forall fun v => hC _ ?_)
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le_max ((Real.norm_eq_abs _).le.trans (hcK v)) (hwK v)

variable {c : V → ℝ} {w : V → Fin m → ℝ}

lemma cont_rowG (t : ℝ) (ν : Fin m → ℝ) :
    Continuous (fun p : ℝ × (Fin m → ℝ) => p.1 + √t * (ν ⬝ᵥ p.2)) :=
  continuous_fst.add (continuous_const.mul (continuous_const.dotProduct continuous_snd))

lemma int_relu_pow (hc : Measurable c) (hw : Measurable w) {Kc K : ℝ} (hcK : ∀ v, |c v| ≤ Kc)
    (hwK : ∀ v, ‖w v‖ ≤ K) (t : ℝ) (ν : Fin m → ℝ) (k : ℕ) :
    Integrable (fun v => relu (rowG c w t ν v) ^ k) μ :=
  int_pair hc hw hcK hwK ((continuous_relu.comp (cont_rowG t ν)).pow k)

lemma int_rowG_pow (hc : Measurable c) (hw : Measurable w) {Kc K : ℝ} (hcK : ∀ v, |c v| ≤ Kc)
    (hwK : ∀ v, ‖w v‖ ≤ K) (t : ℝ) (ν : Fin m → ℝ) (k : ℕ) :
    Integrable (fun v => rowG c w t ν v ^ k) μ :=
  int_pair hc hw hcK hwK ((cont_rowG t ν).pow k)

lemma rowV_eq (hc : Measurable c) (hw : Measurable w) {Kc K : ℝ} (hcK : ∀ v, |c v| ≤ Kc)
    (hwK : ∀ v, ‖w v‖ ≤ K) (t : ℝ) (ν : Fin m → ℝ) :
    rowV μ c w t ν = ∫ v, (relu (rowG c w t ν v) - ∫ v', relu (rowG c w t ν v') ∂μ) ^ 2 ∂μ := by
  unfold rowV
  rw [BstLean.Part183.int_sq_sub_mean]
  · simpa using int_relu_pow (μ := μ) hc hw hcK hwK t ν 1
  · exact int_relu_pow hc hw hcK hwK t ν 2

/-- **(R3a)** `0 ≤ rowV`. -/
lemma rowV_nonneg (hc : Measurable c) (hw : Measurable w) {Kc K : ℝ} (hcK : ∀ v, |c v| ≤ Kc)
    (hwK : ∀ v, ‖w v‖ ≤ K) (t : ℝ) (ν : Fin m → ℝ) : 0 ≤ rowV μ c w t ν := by
  rw [rowV_eq hc hw hcK hwK]; exact integral_nonneg fun v => sq_nonneg _

/-- **(R3)** `Var_v ReLU(g) ≤ Var_v g` (ReLU is `1`-Lipschitz). -/
theorem rowV_le_var (hc : Measurable c) (hw : Measurable w) {Kc K : ℝ} (hcK : ∀ v, |c v| ≤ Kc)
    (hwK : ∀ v, ‖w v‖ ≤ K) (t : ℝ) (ν : Fin m → ℝ) :
    rowV μ c w t ν ≤ ∫ v, (rowG c w t ν v - ∫ v', rowG c w t ν v' ∂μ) ^ 2 ∂μ := by
  set R := fun v => relu (rowG c w t ν v)
  set g := fun v => rowG c w t ν v
  set a := relu (∫ v', g v' ∂μ)
  have iR : Integrable R μ := by simpa using int_relu_pow (μ := μ) hc hw hcK hwK t ν 1
  have iR2 : Integrable (fun v => R v ^ 2) μ := int_relu_pow hc hw hcK hwK t ν 2
  have ig : Integrable g μ := by simpa using int_rowG_pow (μ := μ) hc hw hcK hwK t ν 1
  have ig2 : Integrable (fun v => g v ^ 2) μ := int_rowG_pow hc hw hcK hwK t ν 2
  -- `E(R − a)² = Var R + (ER − a)²`
  have e1 : ∫ v, (R v - a) ^ 2 ∂μ = rowV μ c w t ν + (∫ v, R v ∂μ - a) ^ 2 := by
    have hA : (fun v => (R v - a) ^ 2) = fun v => R v ^ 2 - 2 * a * R v + a ^ 2 := by
      funext v; ring
    have h1 : Integrable (fun v => R v ^ 2 - 2 * a * R v) μ := iR2.sub (iR.const_mul (2 * a))
    rw [hA]
    calc ∫ v, (R v ^ 2 - 2 * a * R v + a ^ 2) ∂μ
        = ∫ v, (R v ^ 2 - 2 * a * R v) ∂μ + ∫ _v, a ^ 2 ∂μ := integral_add h1 (integrable_const _)
      _ = (∫ v, R v ^ 2 ∂μ - ∫ v, 2 * a * R v ∂μ) + a ^ 2 := by
          rw [integral_sub iR2 (iR.const_mul _)]; simp
      _ = _ := by rw [integral_const_mul]; unfold rowV; ring
  have h1 : rowV μ c w t ν ≤ ∫ v, (R v - a) ^ 2 ∂μ := by rw [e1]; nlinarith [sq_nonneg (∫ v, R v ∂μ - a)]
  refine h1.trans (integral_mono ?_ ?_ fun v => ?_)
  · have : (fun v => (R v - a) ^ 2) = fun v => R v ^ 2 - 2 * a * R v + a ^ 2 := by funext v; ring
    rw [this]; exact (iR2.sub (iR.const_mul _)).add (integrable_const _)
  · have : (fun v => (g v - ∫ v', g v' ∂μ) ^ 2) =
        fun v => g v ^ 2 - 2 * (∫ v', g v' ∂μ) * g v + (∫ v', g v' ∂μ) ^ 2 := by funext v; ring
    simp only [g] at this ⊢
    rw [this]; exact (ig2.sub (ig.const_mul _)).add (integrable_const _)
  · have := relu_lip (g v) (∫ v', g v' ∂μ)
    have h2 := sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
    simpa [R, g, a] using h2

end row

section gmomrow
variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]

/-- `(ξ ⬝ᵥ v)^{2p}` is integrable under the standard Gaussian. -/
lemma int_dot_pow {ι : Type} [Fintype ι] (v : ι → ℝ) (p : ℕ) :
    Integrable (fun ξ : ι → ℝ => (ξ ⬝ᵥ v) ^ (2 * p)) (stdGauss ι) := by
  rcases Nat.eq_zero_or_pos p with h0 | hp
  · subst h0; simp
  have hm : AEMeasurable (fun ξ : ι → ℝ => ξ ⬝ᵥ v) (stdGauss ι) :=
    (continuous_id.dotProduct continuous_const).measurable.aemeasurable
  have hg : Integrable (fun x : ℝ => ‖x‖ ^ (2 * p)) (gaussianReal 0 (v ⬝ᵥ v).toNNReal) :=
    (memLp_id_gaussianReal (μ := 0) (v := (v ⬝ᵥ v).toNNReal) ((2 * p : ℕ) : NNReal)).integrable_norm_pow
      (by omega)
  rw [← BstLean.Part131.stdGauss_dot v] at hg
  have := (integrable_map_measure (g := fun x : ℝ => ‖x‖ ^ (2 * p))
    (by fun_prop) hm).mp hg
  refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Function.comp, Real.norm_eq_abs]
  exact (Even.pow_abs ⟨p, by ring⟩ _)

/-- `E(ξ ⬝ᵥ v)^{2p} = E|g|^{2p}·|v|^{2p}`. -/
lemma int_dot_pow_eq {ι : Type} [Fintype ι] (v : ι → ℝ) (p : ℕ) :
    ∫ ξ, (ξ ⬝ᵥ v) ^ (2 * p) ∂stdGauss ι = gmom (2 * p) * (v ⬝ᵥ v) ^ p := by
  have h := BstLean.Part162.gauss_dot_mom v (2 * p)
  have hD : 0 ≤ v ⬝ᵥ v := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have e1 : (fun y : ι → ℝ => |y ⬝ᵥ v| ^ (2 * p)) = fun y => (y ⬝ᵥ v) ^ (2 * p) :=
    funext fun y => Even.pow_abs ⟨p, by ring⟩ _
  rw [e1] at h
  rw [h, pow_mul, Real.sq_sqrt hD]

/-- The row functional under `gaussMat`: `E((M u)_j)^{2p} = E|g|^{2p}(t|u|²)^p`. -/
lemma gaussMat_row_pow {t : ℝ} (ht : 0 ≤ t) (j : Fin m) (u : Fin m → ℝ) (p : ℕ) :
    ∫⁻ M, ENNReal.ofReal (((M *ᵥ u) j) ^ (2 * p)) ∂gaussMat m m t =
      ENNReal.ofReal (gmom (2 * p) * (t * normSq u) ^ p) := by
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin m) ℝ => ENNReal.ofReal (((M *ᵥ u) j) ^ (2 * p))) :=
    ENNReal.measurable_ofReal.comp ((((continuous_apply j).comp
      (Continuous.matrix_mulVec continuous_id continuous_const)).pow _).measurable)
  rw [BstLean.Part170.gaussMat_eq, lintegral_map hmeas (BstLean.Part170.measurable_matOf t)]
  simp_rw [BstLean.Part183.uRow_mulVec]
  rw [← ofReal_integral_eq_lintegral_ofReal (int_dot_pow _ p)
    (Filter.Eventually.of_forall fun ξ => Even.pow_nonneg ⟨p, by ring⟩ _), int_dot_pow_eq,
    BstLean.Part183.uRow_sq ht]

lemma normSq_vmean_le {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (_hK0 : 0 ≤ K)
    (hK2 : ∀ v, normSq (a v) ≤ K ^ 2) (hKs : ∀ v, ‖a v‖ ≤ K) :
    normSq (vmean μ a) ≤ K ^ 2 := by
  have h1 : ∀ i, (vmean μ a i) ^ 2 ≤ ∫ v, (a v i) ^ 2 ∂μ := fun i => by
    have i1 : Integrable (fun v => a v i) μ := int_comp_bdd ha hKs (continuous_apply i)
    have i2 : Integrable (fun v => a v i ^ 2) μ := int_comp_bdd ha hKs ((continuous_apply i).pow 2)
    have := BstLean.Part183.int_sq_sub_mean i1 i2
    have h0 : 0 ≤ ∫ v, (a v i - ∫ w, a w i ∂μ) ^ 2 ∂μ := integral_nonneg fun v => sq_nonneg _
    unfold vmean; linarith
  calc normSq (vmean μ a) = ∑ i, (vmean μ a i) ^ 2 := rfl
    _ ≤ ∑ i, ∫ v, (a v i) ^ 2 ∂μ := Finset.sum_le_sum fun i _ => h1 i
    _ = ∫ v, normSq (a v) ∂μ := by
        unfold normSq
        exact (integral_finsetSum _ fun i _ => (int_comp_bdd (f := fun y => y i ^ 2) ha hKs
          ((continuous_apply i).pow 2))).symm
    _ ≤ ∫ _v, K ^ 2 ∂μ := integral_mono (int_comp_bdd (f := fun y => normSq y) ha hKs
        (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2)) (integrable_const _) hK2
    _ = K ^ 2 := by simp

lemma normSq_sub_le4 {x y : Fin m → ℝ} {K : ℝ} (hx : normSq x ≤ K ^ 2) (hy : normSq y ≤ K ^ 2) :
    normSq (x - y) ≤ 4 * K ^ 2 := by
  have : normSq (x - y) ≤ 2 * normSq x + 2 * normSq y := by
    unfold normSq; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by simp only [Pi.sub_apply]; nlinarith [sq_nonneg (x i + y i)]
  linarith

/-- **(R4) The Gaussian moment of the row variance**: for `M ∼ gaussMat m m t`,
`E_M (E_v ((M(a v − ā))_j)²)^p ≤ E|g|^{2p}·t^p·(4K²)^{p−1}·E_v|a v − ā|²`. -/
theorem row_var_mom {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK0 : 0 ≤ K)
    (hK2 : ∀ v, normSq (a v) ≤ K ^ 2) {t : ℝ} (ht : 0 ≤ t) (j : Fin m) {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ M, ENNReal.ofReal ((∫ v, ((M *ᵥ (a v - vmean μ a)) j) ^ 2 ∂μ) ^ p) ∂gaussMat m m t ≤
      ENNReal.ofReal (gmom (2 * p) * t ^ p * (4 * K ^ 2) ^ (p - 1) *
        ∫ v, normSq (a v - vmean μ a) ∂μ) := by
  have hKs : ∀ v, ‖a v‖ ≤ K := fun v => by
    refine (pi_norm_le_iff_of_nonneg hK0).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    have : a v i ^ 2 ≤ K ^ 2 := by
      have := Finset.single_le_sum (f := fun k => a v k ^ 2) (fun k _ => sq_nonneg _)
        (Finset.mem_univ i)
      exact this.trans (hK2 v)
    exact abs_le_of_sq_le_sq' this hK0 |>.2 |> fun h => abs_le.mpr ⟨(abs_le_of_sq_le_sq' this hK0).1, h⟩
  set ab := vmean μ a
  have hab : normSq ab ≤ K ^ 2 := normSq_vmean_le ha hK0 hK2 hKs
  have hu : ∀ v, normSq (a v - ab) ≤ 4 * K ^ 2 := fun v => normSq_sub_le4 (hK2 v) hab
  have cX : ∀ (M : Matrix (Fin m) (Fin m) ℝ) (k : ℕ),
      Continuous (fun y : Fin m → ℝ => ((M *ᵥ (y - ab)) j) ^ k) := fun M k =>
    ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
      (continuous_id.sub continuous_const))).pow k
  -- Jensen in `v`
  have hJ : ∀ M : Matrix (Fin m) (Fin m) ℝ,
      (∫ v, ((M *ᵥ (a v - ab)) j) ^ 2 ∂μ) ^ p ≤ ∫ v, ((M *ᵥ (a v - ab)) j) ^ (2 * p) ∂μ := by
    intro M
    have h := (convexOn_pow p).map_integral_le (μ := μ) (f := fun v => ((M *ᵥ (a v - ab)) j) ^ 2)
      (continuous_pow p).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun v => Set.mem_Ici.mpr (sq_nonneg _))
      (int_comp_bdd ha hKs (cX M 2))
      (by
        have := int_comp_bdd (μ := μ) ha hKs (cX M (2 * p))
        refine this.congr (Filter.Eventually.of_forall fun v => ?_)
        simp only [Function.comp, ← pow_mul])
    simpa [Function.comp, ← pow_mul] using h
  have mF : Measurable (Function.uncurry fun (M : Matrix (Fin m) (Fin m) ℝ) (v : V) =>
      ENNReal.ofReal (((M *ᵥ (a v - ab)) j) ^ (2 * p))) := by
    have : Continuous (fun q : Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) =>
        ((q.1 *ᵥ (q.2 - ab)) j) ^ (2 * p)) :=
      ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_fst
        (continuous_snd.sub continuous_const))).pow _
    exact ENNReal.measurable_ofReal.comp (this.measurable.comp
      (measurable_fst.prodMk (ha.comp measurable_snd)))
  calc ∫⁻ M, ENNReal.ofReal ((∫ v, ((M *ᵥ (a v - ab)) j) ^ 2 ∂μ) ^ p) ∂gaussMat m m t
      ≤ ∫⁻ M, ∫⁻ v, ENNReal.ofReal (((M *ᵥ (a v - ab)) j) ^ (2 * p)) ∂μ ∂gaussMat m m t := by
        refine lintegral_mono fun M => ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (int_comp_bdd ha hKs (cX M (2 * p)))
          (Filter.Eventually.of_forall fun v => Even.pow_nonneg ⟨p, by ring⟩ _)]
        exact ENNReal.ofReal_le_ofReal (hJ M)
    _ = ∫⁻ v, ∫⁻ M, ENNReal.ofReal (((M *ᵥ (a v - ab)) j) ^ (2 * p)) ∂gaussMat m m t ∂μ :=
        lintegral_lintegral_swap mF.aemeasurable
    _ = ∫⁻ v, ENNReal.ofReal (gmom (2 * p) * (t * normSq (a v - ab)) ^ p) ∂μ :=
        lintegral_congr fun v => gaussMat_row_pow ht j _ p
    _ ≤ ∫⁻ v, ENNReal.ofReal (gmom (2 * p) * t ^ p * (4 * K ^ 2) ^ (p - 1) *
          normSq (a v - ab)) ∂μ := by
        refine lintegral_mono fun v => ENNReal.ofReal_le_ofReal ?_
        have hn0 : 0 ≤ normSq (a v - ab) := Finset.sum_nonneg fun i _ => sq_nonneg _
        have e : (t * normSq (a v - ab)) ^ p = t ^ p * (normSq (a v - ab) ^ (p - 1) *
            normSq (a v - ab)) := by
          rw [mul_pow, ← pow_succ, Nat.sub_add_cancel hp]
        rw [e]
        have h1 : normSq (a v - ab) ^ (p - 1) ≤ (4 * K ^ 2) ^ (p - 1) :=
          pow_le_pow_left₀ hn0 (hu v) _
        have := gmom_nonneg (2 * p)
        have htp : 0 ≤ t ^ p := pow_nonneg ht _
        calc gmom (2 * p) * (t ^ p * (normSq (a v - ab) ^ (p - 1) * normSq (a v - ab)))
            = gmom (2 * p) * t ^ p * normSq (a v - ab) * normSq (a v - ab) ^ (p - 1) := by ring
          _ ≤ gmom (2 * p) * t ^ p * normSq (a v - ab) * (4 * K ^ 2) ^ (p - 1) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = _ := by ring
    _ = ENNReal.ofReal (gmom (2 * p) * t ^ p * (4 * K ^ 2) ^ (p - 1) *
          ∫ v, normSq (a v - ab) ∂μ) := by
        rw [← integral_const_mul]
        refine (ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
        · exact (int_comp_bdd (f := fun y => normSq (y - ab)) ha hKs
            (continuous_finsetSum _ fun i _ => ((continuous_apply i).comp
              (continuous_id.sub continuous_const)).pow 2)).const_mul _
        · refine Filter.Eventually.of_forall fun v => ?_
          have := gmom_nonneg (2 * p)
          have : 0 ≤ normSq (a v - ab) := Finset.sum_nonneg fun i _ => sq_nonneg _
          simp only [Pi.zero_apply]; positivity

end gmomrow

section trunc
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The truncation `min(Q, N²)` of a function with `√Q` Lipschitz is Lipschitz. -/
lemma trunc_lip {Q : (ι → ℝ) → ℝ} (hQ0 : ∀ ξ, 0 ≤ Q ξ) {L : ℝ} (hS : EuLip (fun ξ => √(Q ξ)) L)
    (N : ℕ) : EuLip (fun ξ => min (Q ξ) ((N : ℝ) ^ 2)) (2 * N * L) := by
  have hQN_sq : ∀ ξ, min (Q ξ) ((N : ℝ) ^ 2) = (min (√(Q ξ)) (N : ℝ)) ^ 2 := by
    intro ξ
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rcases le_total (√(Q ξ)) (N : ℝ) with h1 | h1
    · rw [min_eq_left h1, Real.sq_sqrt (hQ0 ξ)]
      have : Q ξ ≤ (N : ℝ) ^ 2 := by
        rw [← Real.sq_sqrt (hQ0 ξ)]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rw [min_eq_left this]
    · rw [min_eq_right h1]
      have : (N : ℝ) ^ 2 ≤ Q ξ := by
        rw [← Real.sq_sqrt (hQ0 ξ)]; exact pow_le_pow_left₀ hN0 h1 2
      rw [min_eq_right this]
  intro x y
  simp only
  rw [hQN_sq, hQN_sq]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h0 : ∀ x, 0 ≤ min (√(Q x)) (N : ℝ) := fun x => le_min (Real.sqrt_nonneg _) hN0
  have hLN : |min (√(Q x)) (N : ℝ) - min (√(Q y)) N| ≤ L * √(∑ i, (x i - y i) ^ 2) := by
    have h := abs_min_sub_min_le_max (√(Q x)) (N : ℝ) (√(Q y)) N
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h
    exact h.trans (hS x y)
  have e : (min (√(Q x)) (N : ℝ)) ^ 2 - (min (√(Q y)) N) ^ 2 =
      (min (√(Q x)) (N : ℝ) - min (√(Q y)) N) * (min (√(Q x)) (N : ℝ) + min (√(Q y)) N) := by
    ring
  have hs : |min (√(Q x)) (N : ℝ) + min (√(Q y)) N| ≤ 2 * N := by
    rw [abs_of_nonneg (add_nonneg (h0 x) (h0 y))]
    linarith [min_le_right (√(Q x)) (N : ℝ), min_le_right (√(Q y)) (N : ℝ)]
  have hL0 : 0 ≤ L * √(∑ i, (x i - y i) ^ 2) := (abs_nonneg _).trans hLN
  rw [e, abs_mul]
  calc _ ≤ (L * √(∑ i, (x i - y i) ^ 2)) * (2 * N) :=
        mul_le_mul hLN hs (abs_nonneg _) hL0
    _ = 2 * N * L * √(∑ i, (x i - y i) ^ 2) := by ring

/-- The gradient of the truncation from the local estimate. -/
lemma trunc_grad {Q G : (ι → ℝ) → ℝ} (hG0 : ∀ ξ, 0 ≤ G ξ) {L : ℝ} (hL0 : 0 ≤ L)
    (hloc : ∀ ξ y, |Q y - Q ξ| ≤ 2 * √(G ξ) * (L * √(∑ i, (y i - ξ i) ^ 2)) +
      2 * (L ^ 2 * ∑ i, (y i - ξ i) ^ 2)) (N : ℕ) (ξ : ι → ℝ) :
    BstLean.Part151.gradSq (fun ξ => min (Q ξ) ((N : ℝ) ^ 2)) ξ ≤ 4 * L ^ 2 * G ξ := by
  have key := BstLean.Part153.gradSq_le_of_local (f := fun ξ => min (Q ξ) ((N : ℝ) ^ 2)) (ξ := ξ)
    (ℓ := 2 * √(G ξ) * L) ?_
  · unfold BstLean.Part151.gradSq
    refine key.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt (hG0 ξ)]; ring
  intro δ hδ
  have hcont : Continuous fun y : ι → ℝ => 2 * L ^ 2 * √(∑ i, (y i - ξ i) ^ 2) :=
    continuous_const.mul (Real.continuous_sqrt.comp
      (continuous_finsetSum _ fun i _ => ((continuous_apply i).sub continuous_const).pow 2))
  have hev : ∀ᶠ y in 𝓝 ξ, 2 * L ^ 2 * √(∑ i, (y i - ξ i) ^ 2) < δ := by
    refine Filter.Tendsto.eventually_lt_const ?_ (hcont.tendsto ξ)
    simpa using hδ
  filter_upwards [hev] with y hy
  have hl := hloc ξ y
  have hm : |min (Q y) ((N : ℝ) ^ 2) - min (Q ξ) ((N : ℝ) ^ 2)| ≤ |Q y - Q ξ| := by
    have := abs_min_sub_min_le_max (Q y) ((N : ℝ) ^ 2) (Q ξ) ((N : ℝ) ^ 2)
    rwa [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at this
  set d := √(∑ i, (y i - ξ i) ^ 2) with hdd
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hS2 : ∑ i, (y i - ξ i) ^ 2 = d ^ 2 := by
    rw [hdd, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rw [hS2] at hl
  refine hm.trans (hl.trans ?_)
  have : 2 * (L ^ 2 * d ^ 2) ≤ δ * d := by
    have := mul_le_mul_of_nonneg_right hy.le hd0
    nlinarith
  nlinarith

/-- The limit `N → ∞` of the truncations (Fatou). -/
lemma trunc_limit {Q : (ι → ℝ) → ℝ} (hQ0 : ∀ ξ, 0 ≤ Q ξ) {L : ℝ} (hL0 : 0 ≤ L)
    (hS : EuLip (fun ξ => √(Q ξ)) L) (k : ℕ) {C : ℝ≥0∞}
    (hP : ∀ N : ℕ, ∫⁻ ξ, ENNReal.ofReal (|min (Q ξ) ((N : ℝ) ^ 2) -
      ∫ ξ', min (Q ξ') ((N : ℝ) ^ 2) ∂stdGauss ι| ^ k) ∂stdGauss ι ≤ C) :
    ∫⁻ ξ, ENNReal.ofReal (|Q ξ - ∫ ξ', Q ξ' ∂stdGauss ι| ^ k) ∂stdGauss ι ≤ C := by
  set QN : ℕ → (ι → ℝ) → ℝ := fun N ξ => min (Q ξ) ((N : ℝ) ^ 2) with hQNd
  have iQ : Integrable Q (stdGauss ι) := by
    have := euLip_sq_integrable hL0 hS
    refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
    exact Real.sq_sqrt (hQ0 ζ)
  have hpt : ∀ ξ, ∀ᶠ N : ℕ in atTop, QN N ξ = Q ξ := by
    intro ξ
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge (Q ξ)
    filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
    simp only [QN]
    refine min_eq_left ?_
    have h1 : (N₀ : ℝ) ≤ N := by exact_mod_cast (le_max_left _ _).trans hN
    have h2 : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
    nlinarith
  have hint : Tendsto (fun N : ℕ => ∫ ξ', QN N ξ' ∂stdGauss ι) atTop
      (𝓝 (∫ ξ', Q ξ' ∂stdGauss ι)) := by
    refine tendsto_integral_of_dominated_convergence Q (fun N => ?_) iQ (fun N => ?_) ?_
    · exact ((trunc_lip hQ0 hS N).continuous (by positivity)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hQ0 ξ) (by positivity))]
      exact min_le_left _ _
    · exact Filter.Eventually.of_forall fun ξ => tendsto_nhds_of_eventually_eq (hpt ξ)
  have hlim : ∀ ξ, Tendsto (fun N : ℕ => ENNReal.ofReal (|QN N ξ -
      ∫ ξ', QN N ξ' ∂stdGauss ι| ^ k)) atTop
      (𝓝 (ENNReal.ofReal (|Q ξ - ∫ ξ', Q ξ' ∂stdGauss ι| ^ k))) := by
    intro ξ
    have h1 : Tendsto (fun N : ℕ => QN N ξ - ∫ ξ', QN N ξ' ∂stdGauss ι) atTop
        (𝓝 (Q ξ - ∫ ξ', Q ξ' ∂stdGauss ι)) :=
      (tendsto_nhds_of_eventually_eq (hpt ξ)).sub hint
    have hc : Continuous fun x : ℝ => ENNReal.ofReal (|x| ^ k) :=
      ENNReal.continuous_ofReal.comp (continuous_abs.pow k)
    exact (hc.tendsto _).comp h1
  have mN : ∀ N : ℕ, Measurable (fun ξ => ENNReal.ofReal (|QN N ξ -
      ∫ ξ', QN N ξ' ∂stdGauss ι| ^ k)) := fun N =>
    ENNReal.measurable_ofReal.comp
      ((((trunc_lip hQ0 hS N).continuous (by positivity)).measurable.sub_const _).abs.pow_const k)
  calc ∫⁻ ξ, ENNReal.ofReal (|Q ξ - ∫ ξ', Q ξ' ∂stdGauss ι| ^ k) ∂stdGauss ι
      = ∫⁻ ξ, liminf (fun N : ℕ => ENNReal.ofReal (|QN N ξ -
          ∫ ξ', QN N ξ' ∂stdGauss ι| ^ k)) atTop ∂stdGauss ι :=
        lintegral_congr fun ξ => ((hlim ξ).liminf_eq).symm
    _ ≤ liminf (fun N : ℕ => ∫⁻ ξ, ENNReal.ofReal (|QN N ξ -
          ∫ ξ', QN N ξ' ∂stdGauss ι| ^ k) ∂stdGauss ι) atTop :=
        lintegral_liminf_le mN
    _ ≤ C := Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hP)

/-- **Truncated Gaussian `L^{2p}` Poincaré inequality from a local estimate.** -/
theorem trunc_poinc_p {Q G : (ι → ℝ) → ℝ} (hQ0 : ∀ ξ, 0 ≤ Q ξ) (hG0 : ∀ ξ, 0 ≤ G ξ) {L : ℝ}
    (hL0 : 0 ≤ L) (hS : EuLip (fun ξ => √(Q ξ)) L)
    (hloc : ∀ ξ y, |Q y - Q ξ| ≤ 2 * √(G ξ) * (L * √(∑ i, (y i - ξ i) ^ 2)) +
      2 * (L ^ 2 * ∑ i, (y i - ξ i) ^ 2)) {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ ξ, ENNReal.ofReal (|Q ξ - ∫ ξ', Q ξ' ∂stdGauss ι| ^ (2 * p)) ∂stdGauss ι ≤
      ENNReal.ofReal ((π / 2) ^ (2 * p) * gmom (2 * p) * (4 * L ^ 2) ^ p) *
        ∫⁻ ξ, ENNReal.ofReal (G ξ ^ p) ∂stdGauss ι := by
  refine trunc_limit hQ0 hL0 hS (2 * p) fun N => ?_
  set QN := fun ξ => min (Q ξ) ((N : ℝ) ^ 2)
  have hLN0 : 0 ≤ 2 * (N : ℝ) * L := by positivity
  have hLip := trunc_lip hQ0 hS N
  refine (BstLean.Part162.poincare_p_lint hLN0 hLip (by omega : 1 ≤ 2 * p)).trans ?_
  set g : (ι → ℝ) → ℝ := fun x => √(BstLean.Part151.gradSq QN x) ^ (2 * p)
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  have hgb : ∀ x, g x ≤ (2 * N * L) ^ (2 * p) := fun x => by
    have h1 := BstLean.Part151.gradSq_le hLN0 hLip x
    have h2 : √(BstLean.Part151.gradSq QN x) ≤ 2 * N * L := by
      rw [Real.sqrt_le_left hLN0]; exact h1
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 _
  have ig : Integrable g (stdGauss ι) := by
    refine Integrable.mono' (integrable_const ((2 * N * L) ^ (2 * p)))
      ((BstLean.Part151.measurable_gradSq _).sqrt.pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hgb x
  have hgq : ∀ x, g x ≤ (4 * L ^ 2) ^ p * G x ^ p := fun x => by
    have e : g x = BstLean.Part151.gradSq QN x ^ p := by
      simp only [g]
      rw [pow_mul, Real.sq_sqrt (BstLean.Part151.gradSq_nonneg _ _)]
    rw [e, ← mul_pow]
    exact pow_le_pow_left₀ (BstLean.Part151.gradSq_nonneg _ _) (trunc_grad hG0 hL0 hloc N x) p
  have hgm : ENNReal.ofReal (∫ x, g x ∂stdGauss ι) ≤
      ENNReal.ofReal ((4 * L ^ 2) ^ p) * ∫⁻ ξ, ENNReal.ofReal (G ξ ^ p) ∂stdGauss ι := by
    rw [ofReal_integral_eq_lintegral_ofReal ig (Filter.Eventually.of_forall hg0),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (hgq x)
  have hgm0 := gmom_nonneg (2 * p)
  calc ENNReal.ofReal ((π / 2) ^ (2 * p) * (gmom (2 * p) * ∫ x, g x ∂stdGauss ι))
      = ENNReal.ofReal ((π / 2) ^ (2 * p) * gmom (2 * p)) *
          ENNReal.ofReal (∫ x, g x ∂stdGauss ι) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    _ ≤ ENNReal.ofReal ((π / 2) ^ (2 * p) * gmom (2 * p)) * (ENNReal.ofReal ((4 * L ^ 2) ^ p) *
          ∫⁻ ξ, ENNReal.ofReal (G ξ ^ p) ∂stdGauss ι) := by gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

/-- **Truncated sharp Gaussian Poincaré inequality from a local estimate**:
`Var Q ≤ 4L²·E G`. -/
theorem trunc_poinc_2 {Q G : (ι → ℝ) → ℝ} (hQ0 : ∀ ξ, 0 ≤ Q ξ) (hG0 : ∀ ξ, 0 ≤ G ξ) {L : ℝ}
    (hL0 : 0 ≤ L) (hS : EuLip (fun ξ => √(Q ξ)) L) (hGi : Integrable G (stdGauss ι))
    (hloc : ∀ ξ y, |Q y - Q ξ| ≤ 2 * √(G ξ) * (L * √(∑ i, (y i - ξ i) ^ 2)) +
      2 * (L ^ 2 * ∑ i, (y i - ξ i) ^ 2)) :
    ∫ ξ, (Q ξ - ∫ ξ', Q ξ' ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤ 4 * L ^ 2 * ∫ ξ, G ξ ∂stdGauss ι := by
  have hC0 : 0 ≤ 4 * L ^ 2 * ∫ ξ, G ξ ∂stdGauss ι :=
    mul_nonneg (by positivity) (integral_nonneg hG0)
  have hlin := trunc_limit hQ0 hL0 hS 2 (C := ENNReal.ofReal (4 * L ^ 2 * ∫ ξ, G ξ ∂stdGauss ι))
    (fun N => by
      set QN := fun ξ => min (Q ξ) ((N : ℝ) ^ 2)
      have hLN0 : 0 ≤ 2 * (N : ℝ) * L := by positivity
      have hLip := trunc_lip hQ0 hS N
      have hP := BstLean.Part151.poincare_lip_le hLN0 hLip (hGi.const_mul (4 * L ^ 2))
        (Filter.Eventually.of_forall fun x => trunc_grad hG0 hL0 hloc N x)
      rw [integral_const_mul] at hP
      have hb : ∃ B, ∀ ξ, |QN ξ - ∫ ξ', QN ξ' ∂stdGauss ι| ≤ B := by
        refine ⟨(N : ℝ) ^ 2 + |∫ ξ', QN ξ' ∂stdGauss ι|, fun ξ => ?_⟩
        have : |QN ξ| ≤ (N : ℝ) ^ 2 := by
          rw [abs_of_nonneg (le_min (hQ0 ξ) (by positivity))]; exact min_le_right _ _
        exact (abs_sub _ _).trans (by linarith)
      obtain ⟨B, hB⟩ := hb
      have ii : Integrable (fun ξ => |QN ξ - ∫ ξ', QN ξ' ∂stdGauss ι| ^ 2) (stdGauss ι) := by
        refine Integrable.of_bound ((((hLip.continuous hLN0).measurable.sub_const _).abs.pow_const
          2).aestronglyMeasurable) (B ^ 2) (Filter.Eventually.of_forall fun ξ => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB ξ) 2
      rw [← ofReal_integral_eq_lintegral_ofReal ii (Filter.Eventually.of_forall fun ξ => by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      simpa [sq_abs] using hP)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ξ => sq_nonneg _)
    (by
      have hc : Continuous Q := ((hS.continuous hL0).pow 2).congr fun ξ => Real.sq_sqrt (hQ0 ξ)
      exact ((hc.sub continuous_const).pow 2).aestronglyMeasurable)]
  refine ENNReal.toReal_le_of_le_ofReal hC0 ?_
  simpa [sq_abs] using hlin

end trunc

section rowloc
variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]
variable {c : V → ℝ} {w : V → Fin m → ℝ}

lemma rowG_add (t : ℝ) (ν ν' : Fin m → ℝ) (v : V) :
    rowG c w t ν' v = rowG c w t ν v + √t * ((ν' - ν) ⬝ᵥ w v) := by
  unfold rowG; rw [sub_dotProduct]; ring

/-- The increment `d = √t⟨ν' − ν, w⟩`: integrable, mean zero, `E d² ≤ tΛ|ν' − ν|²`. -/
lemma row_incr (hc : Measurable c) (hw : Measurable w) {Kc K : ℝ} (hcK : ∀ v, |c v| ≤ Kc)
    (hwK : ∀ v, ‖w v‖ ≤ K) (hw0 : ∀ i, ∫ v, w v i ∂μ = 0) {Λ : ℝ}
    (hΛ : ∀ e, ∫ v, (e ⬝ᵥ w v) ^ 2 ∂μ ≤ Λ * normSq e) {t : ℝ} (ht : 0 ≤ t) (δ : Fin m → ℝ) :
    Integrable (fun v => √t * (δ ⬝ᵥ w v)) μ ∧ Integrable (fun v => (√t * (δ ⬝ᵥ w v)) ^ 2) μ ∧
    ∫ v, √t * (δ ⬝ᵥ w v) ∂μ = 0 ∧
    ∫ v, (√t * (δ ⬝ᵥ w v)) ^ 2 ∂μ ≤ t * Λ * ∑ i, δ i ^ 2 := by
  have cD : Continuous (fun p : ℝ × (Fin m → ℝ) => √t * (δ ⬝ᵥ p.2)) :=
    continuous_const.mul (continuous_const.dotProduct continuous_snd)
  have iD : Integrable (fun v => √t * (δ ⬝ᵥ w v)) μ := int_pair (f := fun p => √t * (δ ⬝ᵥ p.2))
    hc hw hcK hwK cD
  have iD2 : Integrable (fun v => (√t * (δ ⬝ᵥ w v)) ^ 2) μ :=
    int_pair (f := fun p => (√t * (δ ⬝ᵥ p.2)) ^ 2) hc hw hcK hwK (cD.pow 2)
  refine ⟨iD, iD2, ?_, ?_⟩
  · rw [integral_const_mul]
    have : ∫ v, δ ⬝ᵥ w v ∂μ = 0 := by
      unfold dotProduct
      rw [integral_finsetSum _ fun i _ => (int_pair (f := fun p => p.2 i) hc hw hcK hwK
        ((continuous_apply i).comp continuous_snd)).const_mul (δ i)]
      exact Finset.sum_eq_zero fun i _ => by rw [integral_const_mul, hw0 i, mul_zero]
    rw [this, mul_zero]
  · calc ∫ v, (√t * (δ ⬝ᵥ w v)) ^ 2 ∂μ = t * ∫ v, (δ ⬝ᵥ w v) ^ 2 ∂μ := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          simp only; rw [mul_pow, Real.sq_sqrt ht]
      _ ≤ t * (Λ * normSq δ) := mul_le_mul_of_nonneg_left (hΛ δ) ht
      _ = t * Λ * ∑ i, δ i ^ 2 := by unfold normSq; ring

/-- **The row local estimate**: `|E(ν') − E(ν)| ≤ 2√(V(ν))·√(tΛ)|ν' − ν| + 2tΛ|ν' − ν|²`. -/
theorem row_local (hc : Measurable c) (hw : Measurable w) {Kc K : ℝ} (hcK : ∀ v, |c v| ≤ Kc)
    (hwK : ∀ v, ‖w v‖ ≤ K) (hw0 : ∀ i, ∫ v, w v i ∂μ = 0) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ e, ∫ v, (e ⬝ᵥ w v) ^ 2 ∂μ ≤ Λ * normSq e) {t : ℝ} (ht : 0 ≤ t)
    (ν ν' : Fin m → ℝ) :
    |rowE μ c w t ν' - rowE μ c w t ν| ≤
      2 * √(rowV μ c w t ν) * (√(t * Λ) * √(∑ i, (ν' i - ν i) ^ 2)) +
        2 * (√(t * Λ) ^ 2 * ∑ i, (ν' i - ν i) ^ 2) := by
  obtain ⟨iD, iD2, hD0, hDs⟩ := row_incr hc hw hcK hwK hw0 hΛ ht (ν' - ν)
  set S := ∑ i, (ν' i - ν i) ^ 2 with hS
  have hDs' : ∫ v, (√t * ((ν' - ν) ⬝ᵥ w v)) ^ 2 ∂μ ≤ t * Λ * S := by
    simpa [hS] using hDs
  set d := fun v => √t * ((ν' - ν) ⬝ᵥ w v)
  set R := fun v => relu (rowG c w t ν v)
  have iR : Integrable R μ := by simpa using int_relu_pow (μ := μ) hc hw hcK hwK t ν 1
  have iR2 : Integrable (fun v => R v ^ 2) μ := int_relu_pow hc hw hcK hwK t ν 2
  have iR'2 : Integrable (fun v => relu (rowG c w t ν' v) ^ 2) μ :=
    int_relu_pow hc hw hcK hwK t ν' 2
  have iRd : Integrable (fun v => R v * d v) μ :=
    int_pair (f := fun p => relu (p.1 + √t * (ν ⬝ᵥ p.2)) * (√t * ((ν' - ν) ⬝ᵥ p.2))) hc hw hcK hwK
      ((continuous_relu.comp (cont_rowG t ν)).mul
        (continuous_const.mul (continuous_const.dotProduct continuous_snd)))
  set E : V → ℝ := fun v => relu (rowG c w t ν' v) ^ 2 - R v ^ 2 - 2 * R v * d v
  have hE : ∀ v, |E v| ≤ 2 * d v ^ 2 := fun v => by
    simp only [E, R, d]; rw [rowG_add t ν ν' v]; exact BstLean.Part183.relu_sq_taylor _ _
  have iE : Integrable E μ := (iR'2.sub iR2).sub (iRd.const_mul 2 |>.congr
    (Filter.Eventually.of_forall fun v => by simp only; ring))
  have hdiff : rowE μ c w t ν' - rowE μ c w t ν = 2 * ∫ v, R v * d v ∂μ + ∫ v, E v ∂μ := by
    unfold rowE
    rw [← integral_sub iR'2 iR2, ← integral_const_mul, ← integral_add (iRd.const_mul 2) iE]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [E, R]; ring
  have hEs : |∫ v, E v ∂μ| ≤ 2 * (t * Λ * S) := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |E v| ∂μ ≤ ∫ v, 2 * d v ^ 2 ∂μ := integral_mono iE.abs (iD2.const_mul 2) hE
      _ = 2 * ∫ v, d v ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ 2 * (t * Λ * S) := by linarith
  have hlin : |∫ v, R v * d v ∂μ| ≤ √(rowV μ c w t ν) * (√(t * Λ) * √S) := by
    refine (BstLean.Part183.row_cs iR iR2 iD iD2 iRd hD0).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hDs'
  have hL2 : √(t * Λ) ^ 2 = t * Λ := Real.sq_sqrt (by positivity)
  rw [hdiff, hL2]
  calc |2 * ∫ v, R v * d v ∂μ + ∫ v, E v ∂μ|
      ≤ |2 * ∫ v, R v * d v ∂μ| + |∫ v, E v ∂μ| := abs_add_le _ _
    _ ≤ 2 * (√(rowV μ c w t ν) * (√(t * Λ) * √S)) + 2 * (t * Λ * S) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
    _ = _ := by ring

lemma rowE_nonneg (t : ℝ) (ν : Fin m → ℝ) : 0 ≤ rowE μ c w t ν :=
  integral_nonneg fun v => sq_nonneg _

/-- **`√E` is Euclidean Lipschitz** with constant `√(tΛ)`. -/
theorem sqrt_rowE_euLip (hc : Measurable c) (hw : Measurable w) {Kc K : ℝ}
    (hcK : ∀ v, |c v| ≤ Kc) (hwK : ∀ v, ‖w v‖ ≤ K) (hw0 : ∀ i, ∫ v, w v i ∂μ = 0) {Λ : ℝ}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ w v) ^ 2 ∂μ ≤ Λ * normSq e) {t : ℝ} (ht : 0 ≤ t) :
    EuLip (fun ν : Fin m → ℝ => √(rowE μ c w t ν)) (√(t * Λ)) := by
  -- one side
  have one : ∀ ν ν' : Fin m → ℝ, √(rowE μ c w t ν') ≤ √(rowE μ c w t ν) +
      √(t * Λ) * √(∑ i, (ν' i - ν i) ^ 2) := by
    intro ν ν'
    obtain ⟨iD, iD2, -, hDs⟩ := row_incr hc hw hcK hwK hw0 hΛ ht (ν' - ν)
    set d := fun v => √t * ((ν' - ν) ⬝ᵥ w v)
    set R := fun v => relu (rowG c w t ν v)
    set e := fun v => relu (rowG c w t ν' v) - R v
    have iR2 : Integrable (fun v => R v ^ 2) μ := int_relu_pow hc hw hcK hwK t ν 2
    have iR'2 : Integrable (fun v => relu (rowG c w t ν' v) ^ 2) μ :=
      int_relu_pow hc hw hcK hwK t ν' 2
    have ce : Continuous (fun p : ℝ × (Fin m → ℝ) =>
        relu (p.1 + √t * (ν' ⬝ᵥ p.2)) - relu (p.1 + √t * (ν ⬝ᵥ p.2))) :=
      (continuous_relu.comp (cont_rowG t ν')).sub (continuous_relu.comp (cont_rowG t ν))
    have ie2 : Integrable (fun v => e v ^ 2) μ := int_pair hc hw hcK hwK (ce.pow 2)
    have iRe : Integrable (fun v => R v * e v) μ :=
      int_pair hc hw hcK hwK ((continuous_relu.comp (cont_rowG t ν)).mul ce)
    have hed : ∀ v, e v ^ 2 ≤ d v ^ 2 := fun v => by
      have h := relu_lip (rowG c w t ν' v) (rowG c w t ν v)
      rw [rowG_add t ν ν' v, add_sub_cancel_left] at h
      simp only [e, R, d]; rw [rowG_add t ν ν' v]
      exact sq_le_sq.mpr h
    have hB : ∫ v, e v ^ 2 ∂μ ≤ t * Λ * ∑ i, (ν' i - ν i) ^ 2 :=
      (integral_mono ie2 iD2 hed).trans (by simpa using hDs)
    set A := ∫ v, R v ^ 2 ∂μ
    set B := ∫ v, e v ^ 2 ∂μ
    have hA0 : 0 ≤ A := integral_nonneg fun v => sq_nonneg _
    have hB0 : 0 ≤ B := integral_nonneg fun v => sq_nonneg _
    have hcs := BstLean.Part170.int_cs iR2 ie2 iRe
    have hsplit : rowE μ c w t ν' = A + 2 * ∫ v, R v * e v ∂μ + B := by
      unfold rowE
      have : (fun v => relu (rowG c w t ν' v) ^ 2) = fun v => R v ^ 2 + 2 * (R v * e v) + e v ^ 2 :=
        funext fun v => by simp only [e]; ring
      rw [this, integral_add (f := fun v => R v ^ 2 + 2 * (R v * e v)) (g := fun v => e v ^ 2)
        (iR2.add (iRe.const_mul 2)) ie2,
        integral_add (f := fun v => R v ^ 2) (g := fun v => 2 * (R v * e v)) iR2 (iRe.const_mul 2),
        integral_const_mul]
    have h1 : rowE μ c w t ν' ≤ (√A + √B) ^ 2 := by
      rw [hsplit]
      have eA := Real.sq_sqrt hA0
      have eB := Real.sq_sqrt hB0
      nlinarith
    have h2 : √(rowE μ c w t ν') ≤ √A + √B := by
      rw [Real.sqrt_le_left (by positivity)]; exact h1
    have h3 : √B ≤ √(t * Λ) * √(∑ i, (ν' i - ν i) ^ 2) := by
      rw [← Real.sqrt_mul (by positivity)]; exact Real.sqrt_le_sqrt hB
    have : √A = √(rowE μ c w t ν) := rfl
    linarith
  intro x y
  have hsym : ∑ i, (y i - x i) ^ 2 = ∑ i, (x i - y i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  have h1 := one y x
  have h2 := one x y
  rw [hsym] at h2
  rw [abs_le]; constructor <;> linarith

end rowloc

section rowmain
variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]
variable {c : V → ℝ} {w : V → Fin m → ℝ}

lemma measurable_relu_rowG (hc : Measurable c) (hw : Measurable w) (t : ℝ) (k : ℕ) :
    Measurable (fun q : (Fin m → ℝ) × V => relu (rowG c w t q.1 q.2) ^ k) := by
  have hcont : Continuous (fun q : (Fin m → ℝ) × (ℝ × (Fin m → ℝ)) =>
      relu (q.2.1 + √t * (q.1 ⬝ᵥ q.2.2)) ^ k) :=
    (continuous_relu.comp ((continuous_fst.comp continuous_snd).add (continuous_const.mul
      (continuous_fst.dotProduct (continuous_snd.comp continuous_snd))))).pow k
  exact hcont.measurable.comp (measurable_fst.prodMk ((hc.comp measurable_snd).prodMk
    (hw.comp measurable_snd)))

lemma measurable_rowV (hc : Measurable c) (hw : Measurable w) (t : ℝ) :
    Measurable (rowV μ c w t) := by
  have h2 := ((measurable_relu_rowG hc hw t 2).stronglyMeasurable.integral_prod_right'
    (ν := μ)).measurable
  have h1 := ((measurable_relu_rowG hc hw t 1).stronglyMeasurable.integral_prod_right'
    (ν := μ)).measurable
  simp only [pow_one] at h1
  exact h2.sub (h1.pow_const 2)

lemma rowV_le_rowE (t : ℝ) (ν : Fin m → ℝ) : rowV μ c w t ν ≤ rowE μ c w t ν := by
  unfold rowV rowE; nlinarith [sq_nonneg (∫ v, relu (rowG c w t ν v) ∂μ)]

/-- **All moments of the row energy are finite.** -/
theorem rowE_pow_integrable (hc : Measurable c) (hw : Measurable w) {Kc K : ℝ}
    (hcK : ∀ v, |c v| ≤ Kc) (hwK : ∀ v, ‖w v‖ ≤ K) (hw0 : ∀ i, ∫ v, w v i ∂μ = 0) {Λ : ℝ}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ w v) ^ 2 ∂μ ≤ Λ * normSq e) {t : ℝ} (ht : 0 ≤ t)
    (k : ℕ) : Integrable (fun ν => rowE μ c w t ν ^ k) (stdGauss (Fin m)) := by
  have hS := sqrt_rowE_euLip (μ := μ) hc hw hcK hwK hw0 hΛ0 hΛ ht
  have hL0 : 0 ≤ √(t * Λ) := Real.sqrt_nonneg _
  obtain ⟨iX, -⟩ := BstLean.Part152.gaussConc_moment hL0 hS k
  set S := fun ν => √(rowE μ c w t ν)
  set a := ∫ y, S y ∂stdGauss (Fin m)
  have ha : 0 ≤ a := integral_nonneg fun y => Real.sqrt_nonneg _
  refine Integrable.mono' ((iX.add (integrable_const (a ^ (2 * k)))).const_mul (2 ^ (2 * k)))
    ((((hS.continuous hL0).pow 2).congr fun ν => Real.sq_sqrt (rowE_nonneg t ν)).pow k
      |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun ν => ?_)
  set X := max (S ν - a) 0
  have hX0 : 0 ≤ X := le_max_right _ _
  have hSX : S ν ≤ a + X := by have := le_max_left (S ν - a) 0; simp only [X]; linarith
  have e : rowE μ c w t ν ^ k = S ν ^ (2 * k) := by
    simp only [S]; rw [pow_mul, Real.sq_sqrt (rowE_nonneg t ν)]
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (rowE_nonneg t ν) k), e]
  have h1 : S ν ^ (2 * k) ≤ (a + X) ^ (2 * k) := pow_le_pow_left₀ (Real.sqrt_nonneg _) hSX _
  have h2 : (a + X) ^ (2 * k) ≤ (2 * max a X) ^ (2 * k) :=
    pow_le_pow_left₀ (by positivity) (by linarith [le_max_left a X, le_max_right a X]) _
  have h3 : (max a X) ^ (2 * k) ≤ a ^ (2 * k) + X ^ (2 * k) := by
    rcases le_total a X with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ha (2 * k)]
    · rw [max_eq_left h]; linarith [pow_nonneg hX0 (2 * k)]
  calc S ν ^ (2 * k) ≤ (2 * max a X) ^ (2 * k) := h1.trans h2
    _ = 2 ^ (2 * k) * (max a X) ^ (2 * k) := mul_pow _ _ _
    _ ≤ 2 ^ (2 * k) * (X ^ (2 * k) + a ^ (2 * k)) := by
        gcongr; linarith

/-- **(R1) Sharp variance of the row energy**: `Var_ν E(ν) ≤ 4tΛ·E_ν V(ν)`. -/
theorem row_var_sharp (hc : Measurable c) (hw : Measurable w) {Kc K : ℝ}
    (hcK : ∀ v, |c v| ≤ Kc) (hwK : ∀ v, ‖w v‖ ≤ K) (hw0 : ∀ i, ∫ v, w v i ∂μ = 0) {Λ : ℝ}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ w v) ^ 2 ∂μ ≤ Λ * normSq e) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ν, (rowE μ c w t ν - ∫ ν', rowE μ c w t ν' ∂stdGauss (Fin m)) ^ 2 ∂stdGauss (Fin m) ≤
      4 * (t * Λ) * ∫ ν, rowV μ c w t ν ∂stdGauss (Fin m) := by
  have hS := sqrt_rowE_euLip (μ := μ) hc hw hcK hwK hw0 hΛ0 hΛ ht
  have iE : Integrable (rowE μ c w t) (stdGauss (Fin m)) := by
    simpa using rowE_pow_integrable (μ := μ) hc hw hcK hwK hw0 hΛ0 hΛ ht 1
  have iV : Integrable (rowV μ c w t) (stdGauss (Fin m)) :=
    Integrable.mono' iE (measurable_rowV hc hw t).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ν => by
        rw [Real.norm_eq_abs, abs_of_nonneg (rowV_nonneg hc hw hcK hwK t ν)]
        exact rowV_le_rowE t ν)
  have h := trunc_poinc_2 (fun ν => rowE_nonneg (μ := μ) (c := c) (w := w) t ν)
    (rowV_nonneg hc hw hcK hwK t) (Real.sqrt_nonneg _) hS iV
    (fun ξ y => row_local hc hw hcK hwK hw0 hΛ0 hΛ ht ξ y)
  rwa [Real.sq_sqrt (by positivity)] at h

/-- **(R2) Higher moments of the row energy** (truncated Gaussian `L^{2p}` Poincaré):
`E|E(ν) − E E|^{2p} ≤ (π/2)^{2p}·E|g|^{2p}·(4tΛ)^p·E V(ν)^p`. -/
theorem row_mom_p (hc : Measurable c) (hw : Measurable w) {Kc K : ℝ}
    (hcK : ∀ v, |c v| ≤ Kc) (hwK : ∀ v, ‖w v‖ ≤ K) (hw0 : ∀ i, ∫ v, w v i ∂μ = 0) {Λ : ℝ}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ w v) ^ 2 ∂μ ≤ Λ * normSq e) {t : ℝ} (ht : 0 ≤ t)
    {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ ν, ENNReal.ofReal (|rowE μ c w t ν - ∫ ν', rowE μ c w t ν' ∂stdGauss (Fin m)| ^ (2 * p))
      ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((π / 2) ^ (2 * p) * gmom (2 * p) * (4 * (t * Λ)) ^ p) *
        ∫⁻ ν, ENNReal.ofReal (rowV μ c w t ν ^ p) ∂stdGauss (Fin m) := by
  have hS := sqrt_rowE_euLip (μ := μ) hc hw hcK hwK hw0 hΛ0 hΛ ht
  have h := trunc_poinc_p (fun ν => rowE_nonneg (μ := μ) (c := c) (w := w) t ν)
    (rowV_nonneg hc hw hcK hwK t) (Real.sqrt_nonneg _) hS
    (fun ξ y => row_local hc hw hcK hwK hw0 hΛ0 hΛ ht ξ y) hp
  rwa [Real.sq_sqrt (by positivity)] at h

end rowmain

end BstLean.Part184

#print axioms BstLean.Part184.rowV_le_var
#print axioms BstLean.Part184.row_var_mom
#print axioms BstLean.Part184.row_var_sharp
#print axioms BstLean.Part184.row_mom_p
#print axioms BstLean.Part184.rowE_pow_integrable
