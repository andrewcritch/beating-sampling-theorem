import BstLean.Part132Defs

/-!
# Part 132, item 1: the mean of `J` as kernel averages

Role: `delegations/statements/p132-spec.md`. Paper source: `onW2c-cx.md` (16), (18):
`J = (3/2)(P_A + P_{A′}) − 2P_{AA′} − (V_A + V_{A′})/2`, `E J = 3b₂ − 2b₁₁ − S`, `S = 4/n`.

* `Jall_toAll`: the identity for `J` at every point `(W, (A, (A′, F)))`.
* `kern_diag_mean`: `E_{A,F} (2/m_F)|H_A(x)|² = 4/n` for every unit `x` (the scale `S`).
* **`meanJ_eq`**: `∫ Jall d(lawAll) = 3·b2 − 2·b11 − 4/n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131

variable {N mW n mA mF : ℕ}

/-! ## The identity for two vector-valued functions under one probability measure -/

lemma dotp_self {ι : Type*} [Fintype ι] (v : ι → ℝ) : dotp v v = normSq v := by
  simp [dotp, normSq, sq]

section abstract

variable {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ] {d : ℕ}

lemma dot_prod_integral (c : ℝ) (H H' : X → Fin d → ℝ) (hH : ∀ i, Integrable (fun x => H x i) ρ)
    (hH' : ∀ i, Integrable (fun x => H' x i) ρ) :
    ∫ z : X × X, c * dotp (H z.1) (H' z.2) ∂(ρ.prod ρ) =
      c * ∑ i, (∫ x, H x i ∂ρ) * ∫ x, H' x i ∂ρ := by
  rw [integral_const_mul]
  congr 1
  unfold dotp
  rw [integral_finsetSum _ fun i _ => (hH i).mul_prod (hH' i)]
  exact Finset.sum_congr rfl fun i _ => integral_prod_mul (fun x => H x i) (fun x => H' x i)

lemma dot_diag_integral (c : ℝ) (H : X → Fin d → ℝ)
    (hH2 : ∀ i, Integrable (fun x => H x i ^ 2) ρ) :
    ∫ x, c * dotp (H x) (H x) ∂ρ = c * ∑ i, ∫ x, H x i ^ 2 ∂ρ := by
  rw [integral_const_mul]
  congr 1
  simp_rw [dotp_self]
  unfold normSq
  rw [integral_finsetSum _ fun i _ => hH2 i]

lemma cov_diag_integral (H : X → Fin d → ℝ) (hH : ∀ i, Integrable (fun x => H x i) ρ)
    (hH2 : ∀ i, Integrable (fun x => H x i ^ 2) ρ) (i : Fin d) :
    ∫ x, (H x i - ∫ y, H y i ∂ρ) * (H x i - ∫ y, H y i ∂ρ) ∂ρ =
      ∫ x, H x i ^ 2 ∂ρ - (∫ x, H x i ∂ρ) * ∫ x, H x i ∂ρ := by
  set a := ∫ y, H y i ∂ρ with ha
  have e : (fun x => (H x i - a) * (H x i - a)) = fun x => H x i ^ 2 - 2 * a * H x i + a ^ 2 := by
    funext x; ring
  have h1 : Integrable (fun x => H x i ^ 2 - 2 * a * H x i) ρ := (hH2 i).sub ((hH i).const_mul _)
  have a1 := integral_add h1 (integrable_const (a ^ 2))
  have a2 := integral_sub (hH2 i) ((hH i).const_mul (2 * a))
  have a3 : ∫ x, 2 * a * H x i ∂ρ = 2 * a * ∫ x, H x i ∂ρ := integral_const_mul _ _
  have a4 : ∫ _x : X, a ^ 2 ∂ρ = a ^ 2 := by simp
  beta_reduce at a1 a2
  rw [e, a1, a2, a3, a4, ← ha]
  ring

/-- The algebra of `J = D − T̄` for two families of functions under one probability measure. -/
theorem J_abstract (c : ℝ) (H H' : X → Fin d → ℝ) (hH : ∀ i, Integrable (fun x => H x i) ρ)
    (hH2 : ∀ i, Integrable (fun x => H x i ^ 2) ρ) (hH' : ∀ i, Integrable (fun x => H' x i) ρ)
    (hH2' : ∀ i, Integrable (fun x => H' x i ^ 2) ρ) :
    c * normSq ((fun i => ∫ x, H x i ∂ρ) - fun i => ∫ x, H' x i ∂ρ) -
      c * (1 / 2 * ((∑ i, ∫ x, (H x i - ∫ y, H y i ∂ρ) * (H x i - ∫ y, H y i ∂ρ) ∂ρ) +
        ∑ i, ∫ x, (H' x i - ∫ y, H' y i ∂ρ) * (H' x i - ∫ y, H' y i ∂ρ) ∂ρ)) =
    3 / 2 * (∫ z : X × X, c * dotp (H z.1) (H z.2) ∂(ρ.prod ρ) +
        ∫ z : X × X, c * dotp (H' z.1) (H' z.2) ∂(ρ.prod ρ)) -
      2 * ∫ z : X × X, c * dotp (H z.1) (H' z.2) ∂(ρ.prod ρ) -
      (∫ x, c * dotp (H x) (H x) ∂ρ + ∫ x, c * dotp (H' x) (H' x) ∂ρ) / 2 := by
  rw [dot_prod_integral ρ c H H hH hH, dot_prod_integral ρ c H' H' hH' hH',
    dot_prod_integral ρ c H H' hH hH', dot_diag_integral ρ c H hH2, dot_diag_integral ρ c H' hH2']
  simp_rw [cov_diag_integral ρ H hH hH2, cov_diag_integral ρ H' hH' hH2']
  have e1 : normSq ((fun i => ∫ x, H x i ∂ρ) - fun i => ∫ x, H' x i ∂ρ) =
      (∑ i, (∫ x, H x i ∂ρ) * ∫ x, H x i ∂ρ) - 2 * (∑ i, (∫ x, H x i ∂ρ) * ∫ x, H' x i ∂ρ) +
        ∑ i, (∫ x, H' x i ∂ρ) * ∫ x, H' x i ∂ρ := by
    unfold normSq
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]
    ring
  rw [e1, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

end abstract

/-! ## From `μ_W` to the inputs `u` -/

lemma muWn_prod_integral (hN : 1 ≤ N) (W : MlpParam N mW n) {g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (hg : Measurable g) :
    ∫ z, g z ∂((muWn W).prod (muWn W)) = ∫ uu, g (xW W uu.1, xW W uu.2) ∂lawU2 N := by
  have := uniformSphere_isProbability N hN
  have hm : Measurable (fun u => sphPt (mlpEval W u)) := measurable_sphPt_mlpEval W
  unfold muWn lawU2
  rw [Measure.map_prod_map _ _ hm hm, integral_map (hm.prodMap hm).aemeasurable
    hg.aestronglyMeasurable]
  rfl

lemma muWn_diag_integral (hN : 1 ≤ N) (W : MlpParam N mW n) {g : (Fin n → ℝ) → ℝ}
    (hg : Measurable g) :
    ∫ x, g x ∂muWn W = ∫ uu, g (xW W uu.1) ∂lawU2 N := by
  have := uniformSphere_isProbability N hN
  have hm : Measurable (fun u => sphPt (mlpEval W u)) := measurable_sphPt_mlpEval W
  unfold muWn lawU2
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable,
    integral_fun_fst (fun u => g (xW W u))]
  simp
  rfl

lemma Tn_trace (W : MlpParam N mW n) (A A' : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ)
    (F₂ : Matrix (Fin mF) (Fin mF) ℝ) :
    (((1 : ℝ) / 2) • (covMat W A F₁ F₂ + covMat W A' F₁ F₂)).trace =
      1 / 2 * ((∑ i, covMat W A F₁ F₂ i i) + ∑ i, covMat W A' F₁ F₂ i i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]

/-- **The identity for `J`** at every point: with `P`, `V` written as means over the inputs,
`J = (3/2)(P_A + P_{A′}) − 2P_{AA′} − (V_A + V_{A′})/2`. -/
theorem Jall_toAll (hn : 1 ≤ n) (hN : 1 ≤ N) (r : Rest N mW n mA mF) :
    Jall (toAll r) =
      3 / 2 * (∫ uu, kgen false false false (uu, r) ∂lawU2 N +
          ∫ uu, kgen true true false (uu, r) ∂lawU2 N) -
        2 * ∫ uu, kgen false true false (uu, r) ∂lawU2 N -
        (∫ uu, kgen false false true (uu, r) ∂lawU2 N +
          ∫ uu, kgen true true true (uu, r) ∂lawU2 N) / 2 := by
  obtain ⟨W, A, A', F⟩ := r
  have := muWn_isProbability hN W
  have hH : ∀ B : MlpParam n mA n, ∀ i, Integrable (fun x => hidF F.1 F.2.1 B x i) (muWn W) :=
    fun B i => hidF_integrable hn hN W B F.1 F.2.1 i
  have hH2 : ∀ B : MlpParam n mA n, ∀ i,
      Integrable (fun x => hidF F.1 F.2.1 B x i ^ 2) (muWn W) := fun B i =>
    muWn_integrable_of_continuous hn hN W ((continuous_hidF F.1 F.2.1 B i).pow 2)
  have key := J_abstract (muWn W) (2 / (mF : ℝ)) (hidF F.1 F.2.1 A) (hidF F.1 F.2.1 A')
    (hH A) (hH2 A) (hH A') (hH2 A')
  have hJ : Jall (toAll (W, A, A', F)) =
      2 / (mF : ℝ) * normSq ((fun i => ∫ x, hidF F.1 F.2.1 A x i ∂muWn W) -
        fun i => ∫ x, hidF F.1 F.2.1 A' x i ∂muWn W) -
      2 / (mF : ℝ) * (1 / 2 * ((∑ i, ∫ x, (hidF F.1 F.2.1 A x i - ∫ y, hidF F.1 F.2.1 A y i ∂muWn W) *
          (hidF F.1 F.2.1 A x i - ∫ y, hidF F.1 F.2.1 A y i ∂muWn W) ∂muWn W) +
        ∑ i, ∫ x, (hidF F.1 F.2.1 A' x i - ∫ y, hidF F.1 F.2.1 A' y i ∂muWn W) *
          (hidF F.1 F.2.1 A' x i - ∫ y, hidF F.1 F.2.1 A' y i ∂muWn W) ∂muWn W)) := by
    show Jn W A A' F.1 F.2.1 = _
    unfold Jn Dn Tn
    rw [Tn_trace]
    rfl
  rw [hJ, key]
  have mk : ∀ B B' : MlpParam n mA n, Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      kern F B B' z.1 z.2) := fun B B' =>
    measurable_kern_comp measurable_const measurable_const measurable_const measurable_fst
      measurable_snd
  have md : ∀ B : MlpParam n mA n, Measurable (fun x : Fin n → ℝ => kern F B B x x) := fun B =>
    measurable_kern_comp measurable_const measurable_const measurable_const measurable_id
      measurable_id
  have p1 := muWn_prod_integral hN W (mk A A)
  have p2 := muWn_prod_integral hN W (mk A' A')
  have p3 := muWn_prod_integral hN W (mk A A')
  have p4 := muWn_diag_integral hN W (md A)
  have p5 := muWn_diag_integral hN W (md A')
  unfold kern at p1 p2 p3 p4 p5
  rw [p1, p2, p3, p4, p5]
  rfl

/-! ## The scale `S = 4/n` -/

/-- `E_F |H(y)|² = (m_F/2·2/m_F)·(m_F/2·2/n)·|y|²` for the hidden map of `F`. -/
lemma F_hid_sq (y : Fin n → ℝ) :
    Integrable (fun F : MlpParam n mF 1 => normSq (hid2 F.1 F.2.1 y)) (mlpGauss n mF 1) ∧
    ∫ F : MlpParam n mF 1, normSq (hid2 F.1 F.2.1 y) ∂mlpGauss n mF 1 =
      (mF : ℝ) / 2 * (2 / (mF : ℝ)) * ((mF : ℝ) / 2 * (2 / (n : ℝ))) * normSq y := by
  obtain ⟨hi, he⟩ := hid2_sq (m₁ := mF) (m₂ := mF) (two_div_nonneg n) (two_div_nonneg mF) y
  unfold mlpGauss
  exact ⟨integrable_drop3 hi, by rw [integral_drop3 hi.aestronglyMeasurable, he]⟩

/-- For every `x`: `E_{A,A′,F} (2/m_F)|H_A(x)|² = (4/n)·|x|²`, with integrability. -/
theorem kern_diag_gen (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) (x : Fin n → ℝ) :
    Integrable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.1 x x)
      ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) ∧
    ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1, kern p.2.2 p.1 p.1 x x
      ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) =
      4 / n * normSq x := by
  have hmF' : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : ∀ (F : MlpParam n mF 1) (a : MlpParam n mA n),
      kern F a a x x = 2 / (mF : ℝ) * normSq (hid2 F.1 F.2.1 (mlpEval a x)) := by
    intro F a
    unfold kern hidF
    rw [dotp_self]
  have inner : ∀ a : MlpParam n mA n,
      Integrable (fun y : MlpParam n mA n × MlpParam n mF 1 => kern y.2 a a x x)
        ((mlpGauss n mA n).prod (mlpGauss n mF 1)) ∧
      ∫ y : MlpParam n mA n × MlpParam n mF 1, kern y.2 a a x x
        ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) = 2 / (n : ℝ) * normSq (mlpEval a x) := by
    intro a
    obtain ⟨hi, he⟩ := F_hid_sq (mF := mF) (mlpEval a x)
    simp_rw [hk]
    refine ⟨(hi.const_mul _).comp_snd _, ?_⟩
    rw [integral_fun_snd (fun F : MlpParam n mF 1 =>
      2 / (mF : ℝ) * normSq (hid2 F.1 F.2.1 (mlpEval a x))), integral_const_mul, he]
    simp
    field_simp
  have hmeas : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.1 x x) :=
    measurable_kern_comp (measurable_snd.comp measurable_snd) measurable_fst measurable_fst
      measurable_const measurable_const
  have step := prod_step (μ := mlpGauss n mA n)
    (ν := (mlpGauss n mA n).prod (mlpGauss n mF 1)) hmeas
    (fun p => by rw [hk]; exact mul_nonneg (by positivity) (normSq_nonneg _))
    (fun a => 2 / (n : ℝ) * normSq (mlpEval a x)) inner
    ((mlp_normSq_integrable x).const_mul _)
  refine ⟨step.1, ?_⟩
  rw [step.2, integral_const_mul, agent_second_moment hn hmA]
  ring

/-- **The scale**: for every unit vector `x`, `E_{A,A′,F} (2/m_F)|H_A(x)|² = 4/n`. -/
theorem kern_diag_mean (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) {x : Fin n → ℝ}
    (hx : normSq x = 1) :
    ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1, kern p.2.2 p.1 p.1 x x
      ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) = 4 / n := by
  rw [(kern_diag_gen hn hmA hmF x).2, hx, mul_one]

/-! ## Item 1 -/

lemma kgen_swap (dg : Bool) (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) :
    kgen true true dg ω = kgen false false dg (ω.1, swapA ω.2) := rfl

lemma kgen_swap_integral (hN : 1 ≤ N) (dg : Bool) :
    ∫ ω, kgen (mW := mW) (mA := mA) (mF := mF) (n := n) true true dg ω
      ∂((lawU2 N).prod (lawR N mW n mA mF)) =
    ∫ ω, kgen false false dg ω ∂((lawU2 N).prod (lawR N mW n mA mF)) := by
  have := uniformSphere_isProbability N hN
  have hprob : IsProbabilityMeasure (lawU2 N) := by unfold lawU2; infer_instance
  have h := Measure.map_prod_map (lawU2 N) (lawR N mW n mA mF) (f := id) (g := swapA)
    measurable_id measurable_swapA
  rw [Measure.map_id, lawR_swapA] at h
  simp_rw [kgen_swap]
  have hm : Measurable (Prod.map (id : (Fin N → ℝ) × (Fin N → ℝ) → _)
      (swapA (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF))) :=
    measurable_id.prodMap measurable_swapA
  have h2 := integral_map (μ := (lawU2 N).prod (lawR N mW n mA mF)) hm.aemeasurable
    (f := kgen false false dg) (measurable_kgen false false dg).aestronglyMeasurable
  rw [← h] at h2
  exact h2.symm

lemma kgen_section_integral (hn : 1 ≤ n) (hN : 1 ≤ N) (pa pa' dg : Bool) :
    Integrable (fun r : Rest N mW n mA mF => ∫ uu, kgen pa pa' dg (uu, r) ∂lawU2 N)
      (lawR N mW n mA mF) ∧
    ∫ r, ∫ uu, kgen pa pa' dg (uu, r) ∂lawU2 N ∂lawR N mW n mA mF =
      ∫ ω, kgen pa pa' dg ω ∂((lawU2 N).prod (lawR N mW n mA mF)) := by
  have := uniformSphere_isProbability N hN
  have hprob : IsProbabilityMeasure (lawU2 N) := by unfold lawU2; infer_instance
  have hi := kgen_integrable (mW := mW) (mA := mA) (mF := mF) hn hN pa pa' dg
  exact ⟨hi.integral_prod_right, (integral_prod_symm _ hi).symm⟩

lemma integral_const_of_sections {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (τ : Measure γ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ] {f : α × β × γ → ℝ}
    (hf : Integrable f (μ.prod (ν.prod τ))) {c : ℝ} (h : ∀ a b, ∫ z, f (a, (b, z)) ∂τ = c) :
    ∫ ω, f ω ∂(μ.prod (ν.prod τ)) = c := by
  rw [integral_prod _ hf]
  have hae : ∀ᵐ a ∂μ, ∫ y, f (a, y) ∂(ν.prod τ) = c := by
    filter_upwards [hf.prod_right_ae] with a ha
    rw [integral_prod _ ha]
    simp_rw [h a]
    simp
  rw [integral_congr_ae hae]
  simp

lemma kgen_diag_eq (uu : (Fin N → ℝ) × (Fin N → ℝ)) (w : MlpParam N mW n)
    (p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) :
    kgen false false true (uu, (w, p)) = kern p.2.2 p.1 p.1 (xW w uu.1) (xW w uu.1) := rfl

lemma kgen_diag_section (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    (uu : (Fin N → ℝ) × (Fin N → ℝ)) (w : MlpParam N mW n) :
    ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1, kgen false false true (uu, (w, p))
      ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) = 4 / n := by
  simp only [kgen_diag_eq]
  exact kern_diag_mean hn hmA hmF (normSq_xW hn w uu.1)

/-- The mean of the diagonal term: `E V_A = 4/n`. -/
theorem kgen_diag_mean (hn : 1 ≤ n) (hN : 1 ≤ N) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) :
    ∫ ω, kgen (mW := mW) (mA := mA) (mF := mF) false false true ω
      ∂((lawU2 N).prod (lawR N mW n mA mF)) = 4 / n := by
  have := uniformSphere_isProbability N hN
  have hprob : IsProbabilityMeasure (lawU2 N) := by unfold lawU2; infer_instance
  have hi := kgen_integrable (mW := mW) (mA := mA) (mF := mF) hn hN false false true
  exact integral_const_of_sections (lawU2 N) (mlpGauss N mW n)
    ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
    (f := kgen false false true) hi (kgen_diag_section hn hmA hmF)

/-- **Item 1: the mean of `J` as kernel averages.** `E J = 3·b₂ − 2·b₁₁ − S`, `S = 4/n`:
the mean of `Jall` under the distribution `lawAll` of the four networks (Part 131) equals
`3·b2 − 2·b11 − 4/n`. -/
theorem meanJ_eq (hn : 1 ≤ n) (hN : 1 ≤ N) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) :
    ∫ t, Jall t ∂lawAll N mW n mA mF =
      3 * b2 N mW n mA mF - 2 * b11 N mW n mA mF - 4 / n := by
  rw [← lawR_map, integral_map measurable_toAll.aemeasurable
    (by rw [lawR_map]; exact (measurable_Jall hN).aestronglyMeasurable)]
  simp_rw [Jall_toAll hn hN]
  obtain ⟨i1, e1⟩ := kgen_section_integral (mW := mW) (mA := mA) (mF := mF) hn hN false false false
  obtain ⟨i2, e2⟩ := kgen_section_integral (mW := mW) (mA := mA) (mF := mF) hn hN true true false
  obtain ⟨i3, e3⟩ := kgen_section_integral (mW := mW) (mA := mA) (mF := mF) hn hN false true false
  obtain ⟨i4, e4⟩ := kgen_section_integral (mW := mW) (mA := mA) (mF := mF) hn hN false false true
  obtain ⟨i5, e5⟩ := kgen_section_integral (mW := mW) (mA := mA) (mF := mF) hn hN true true true
  have a1 := integral_sub (((i1.add i2).const_mul (3 / 2)).sub (i3.const_mul 2))
    ((i4.add i5).div_const 2)
  have a2 := integral_sub ((i1.add i2).const_mul (3 / 2)) (i3.const_mul 2)
  have a3 := integral_const_mul (μ := lawR N mW n mA mF) (3 / 2 : ℝ)
    (fun r => (∫ uu, kgen false false false (uu, r) ∂lawU2 N) +
      ∫ uu, kgen true true false (uu, r) ∂lawU2 N)
  have a4 := integral_add i1 i2
  have a5 := integral_const_mul (μ := lawR N mW n mA mF) (2 : ℝ)
    (fun r => ∫ uu, kgen false true false (uu, r) ∂lawU2 N)
  have a6 := integral_div (μ := lawR N mW n mA mF) (2 : ℝ)
    (fun r => (∫ uu, kgen false false true (uu, r) ∂lawU2 N) +
      ∫ uu, kgen true true true (uu, r) ∂lawU2 N)
  have a7 := integral_add i4 i5
  simp only [Pi.add_apply, Pi.sub_apply] at a1 a2 a3 a4 a5 a6 a7
  rw [a1, a2, a3, a4, a5, a6, a7, e1, e2, e3, e4, e5, kgen_swap_integral hN false,
    kgen_swap_integral hN true, kgen_diag_mean hn hN hmA hmF, ← b2_eq, ← b11_eq]
  ring

end BstLean.Part132

open BstLean.Part132 in
#print axioms Jall_toAll
open BstLean.Part132 in
#print axioms kern_diag_mean
open BstLean.Part132 in
#print axioms meanJ_eq
