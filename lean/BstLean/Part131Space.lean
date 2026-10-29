import BstLean.Part131Net

/-!
# Part 131: the probability space of the four networks, and measurability in the weights

Role: `delegations/statements/p131-spec.md`, items 4 to 6 (definitions and measurability).

The probability space of the four networks is `lawAll N mW n mA mF`, a measure on
`((W, F), (A, A′))`: `W`, `F`, `A`, `A′` independent, each with the random MLP distribution.

* `measurable_Bn`, `measurable_sdn`: the target and the realized spread are jointly measurable in
  `(W, A, F)`.
* `lawWF`, `lawAll`; `sepEvent`: the separation `|B_A − B_{A′}| > (s_A + s_{A′})/2`;
  `Jall`: `J = D − T̄` as a function on that space; `sepProbN`: `Δ(W, F)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part131

open MeasureTheory ProbabilityTheory Set Matrix
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130

universe w

variable {N mW n mA mF : ℕ}

/-! ## Measurability in the weights -/

/-- An integral under `μ_W` of a jointly measurable function is measurable in `W` and the
parameter. -/
lemma measurable_muWn_integral {Q : Type*} [MeasurableSpace Q] (hN : 1 ≤ N)
    (g : Q → (Fin n → ℝ) → ℝ) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun q : MlpParam N mW n × Q => ∫ x, g q.2 x ∂muWn q.1) := by
  have := uniformSphere_isProbability N hN
  have e : ∀ q : MlpParam N mW n × Q, ∫ x, g q.2 x ∂muWn q.1 =
      ∫ u, g q.2 (sphPt (mlpEval q.1 u)) ∂uniformSphere N := by
    intro q
    unfold muWn
    rw [integral_map (measurable_sphPt_mlpEval q.1).aemeasurable]
    exact (hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  simp_rw [e]
  have hjoint : Measurable (fun z : (MlpParam N mW n × Q) × (Fin N → ℝ) =>
      g z.1.2 (sphPt (mlpEval z.1.1 z.2))) :=
    hg.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_sphPt.comp (continuous_mlpEval_joint.measurable.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))))
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable

lemma continuous_phiN_all : Continuous (fun p : (MlpParam n mA n × MlpParam n mF 1) ×
    (Fin n → ℝ) => phiN p.1.1 p.1.2 p.2) := by
  unfold phiN
  exact (continuous_apply 0).comp (continuous_mlpEval_joint.comp
    ((continuous_snd.comp continuous_fst).prodMk
      (continuous_mlpEval_joint.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))))

/-- `B` is jointly measurable in `(W, A, F)`. -/
theorem measurable_Bn (hN : 1 ≤ N) :
    Measurable (fun t : MlpParam N mW n × MlpParam n mA n × MlpParam n mF 1 =>
      Bn t.1 t.2.1 t.2.2) :=
  measurable_muWn_integral hN (fun θ : MlpParam n mA n × MlpParam n mF 1 => phiN θ.1 θ.2)
    continuous_phiN_all.measurable

lemma sdn_eq (W : MlpParam N mW n) (A : MlpParam n mA n) (F : MlpParam n mF 1) :
    sdn W A F = √(∫ x, (phiN A F x - Bn W A F) ^ 2 ∂muWn W) := by
  unfold sdn Bn
  rw [variance_eq_integral (continuous_phiN A F).measurable.aemeasurable]

/-- The realized spread is jointly measurable in `(W, A, F)`. -/
theorem measurable_sdn (hN : 1 ≤ N) :
    Measurable (fun t : MlpParam N mW n × MlpParam n mA n × MlpParam n mF 1 =>
      sdn t.1 t.2.1 t.2.2) := by
  simp_rw [sdn_eq]
  refine Real.continuous_sqrt.measurable.comp ?_
  have hg : Measurable (Function.uncurry
      (fun (θ : (MlpParam n mA n × MlpParam n mF 1) × ℝ) (x : Fin n → ℝ) =>
        (phiN θ.1.1 θ.1.2 x - θ.2) ^ 2)) := by
    have h1 : Measurable (fun p : ((MlpParam n mA n × MlpParam n mF 1) × ℝ) × (Fin n → ℝ) =>
        phiN p.1.1.1 p.1.1.2 p.2) :=
      continuous_phiN_all.measurable.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact (h1.sub (measurable_snd.comp measurable_fst)).pow_const 2
  have h := measurable_muWn_integral (mW := mW) hN _ hg
  have h2 : Measurable (fun t : MlpParam N mW n × MlpParam n mA n × MlpParam n mF 1 =>
      (t.1, (t.2, Bn t.1 t.2.1 t.2.2))) :=
    measurable_fst.prodMk (measurable_snd.prodMk (measurable_Bn hN))
  have h3 := h.comp h2
  simp only [Function.comp_def] at h3
  exact h3

lemma continuous_hidF_all (i : Fin mF) : Continuous (fun p : (MlpParam n mA n ×
    Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ) × (Fin n → ℝ) =>
    hidF p.1.2.1 p.1.2.2 p.1.1 p.2 i) := by
  simp_rw [hidF_eq]
  refine (continuous_apply i).comp (continuous_mlpEval_joint.comp (Continuous.prodMk ?_ ?_))
  · exact (continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk
      ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_const)
  · exact continuous_mlpEval_joint.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)

/-- A coordinate of `a_A` is jointly measurable in `(W, A, F₁, F₂)`. -/
lemma measurable_aVec (hN : 1 ≤ N) (i : Fin mF) :
    Measurable (fun t : MlpParam N mW n × (MlpParam n mA n × Matrix (Fin mF) (Fin n) ℝ ×
      Matrix (Fin mF) (Fin mF) ℝ) => aVec t.1 t.2.1 t.2.2.1 t.2.2.2 i) :=
  measurable_muWn_integral hN (fun (θ : MlpParam n mA n × Matrix (Fin mF) (Fin n) ℝ ×
      Matrix (Fin mF) (Fin mF) ℝ) x => hidF θ.2.1 θ.2.2 θ.1 x i) (continuous_hidF_all i).measurable

/-- A diagonal entry of `Σ_A` is jointly measurable in `(W, A, F₁, F₂)`. -/
lemma measurable_covDiag (hN : 1 ≤ N) (i : Fin mF) :
    Measurable (fun t : MlpParam N mW n × (MlpParam n mA n × Matrix (Fin mF) (Fin n) ℝ ×
      Matrix (Fin mF) (Fin mF) ℝ) => covMat t.1 t.2.1 t.2.2.1 t.2.2.2 i i) := by
  have hg : Measurable (Function.uncurry
      (fun (θ : (MlpParam n mA n × Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ) × ℝ)
        (x : Fin n → ℝ) => (hidF θ.1.2.1 θ.1.2.2 θ.1.1 x i - θ.2) *
          (hidF θ.1.2.1 θ.1.2.2 θ.1.1 x i - θ.2))) := by
    have h1 : Measurable (fun p : ((MlpParam n mA n × Matrix (Fin mF) (Fin n) ℝ ×
        Matrix (Fin mF) (Fin mF) ℝ) × ℝ) × (Fin n → ℝ) =>
        hidF p.1.1.2.1 p.1.1.2.2 p.1.1.1 p.2 i) :=
      (continuous_hidF_all i).measurable.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact (h1.sub (measurable_snd.comp measurable_fst)).mul
      (h1.sub (measurable_snd.comp measurable_fst))
  have h := measurable_muWn_integral (mW := mW) hN _ hg
  have h2 : Measurable (fun t : MlpParam N mW n × (MlpParam n mA n × Matrix (Fin mF) (Fin n) ℝ ×
      Matrix (Fin mF) (Fin mF) ℝ) => (t.1, (t.2, aVec t.1 t.2.1 t.2.2.1 t.2.2.2 i))) :=
    measurable_fst.prodMk (measurable_snd.prodMk (measurable_aVec hN i))
  have h3 := h.comp h2
  simp only [Function.comp_def] at h3
  exact h3

/-! ## The probability space of the four networks -/

/-- The distribution of `(W, F)`: independent, each with the random MLP distribution. -/
noncomputable def lawWF (N mW n mF : ℕ) : Measure (MlpParam N mW n × MlpParam n mF 1) :=
  (mlpGauss N mW n).prod (mlpGauss n mF 1)

/-- The distribution of `((W, F), (A, A′))`: the four networks independent, each with the random
MLP distribution; `A′` is an independent copy of the Agent network. -/
noncomputable def lawAll (N mW n mA mF : ℕ) :
    Measure ((MlpParam N mW n × MlpParam n mF 1) × MlpParam n mA n × MlpParam n mA n) :=
  (lawWF N mW n mF).prod ((mlpGauss n mA n).prod (mlpGauss n mA n))

instance : IsProbabilityMeasure (lawWF N mW n mF) := by unfold lawWF; infer_instance
instance : IsProbabilityMeasure (lawAll N mW n mA mF) := by unfold lawAll; infer_instance

/-- **The separation event** `|B_A − B_{A′}| > (s_A + s_{A′})/2`, a set of `((W, F), (A, A′))`. -/
def sepEvent : Set ((MlpParam N mW n × MlpParam n mF 1) × MlpParam n mA n × MlpParam n mA n) :=
  {t | (sdn t.1.1 t.2.1 t.1.2 + sdn t.1.1 t.2.2 t.1.2) / 2 <
    |Bn t.1.1 t.2.1 t.1.2 - Bn t.1.1 t.2.2 t.1.2|}

/-- `J = D − T̄` as a function of `((W, F), (A, A′))`. It reads `W`, `A`, `A′` and the first two
matrices `F₁ = F.1`, `F₂ = F.2.1` of `F`; it does not read the last matrix `F.2.2`. -/
noncomputable def Jall
    (t : (MlpParam N mW n × MlpParam n mF 1) × MlpParam n mA n × MlpParam n mA n) : ℝ :=
  Jn t.1.1 t.2.1 t.2.2 t.1.2.1 t.1.2.2.1

/-- `Δ(W, F)`: the conditional probability of the separation given `(W, F)`, over two independent
copies `A, A′` of the Agent network (hidden width `mA`). -/
noncomputable def sepProbN (mA : ℕ) (W : MlpParam N mW n) (F : MlpParam n mF 1) : ℝ :=
  ((mlpGauss n mA n).prod (mlpGauss n mA n)).real
    {q | (sdn W q.1 F + sdn W q.2 F) / 2 < |Bn W q.1 F - Bn W q.2 F|}

lemma measurable_Bn' (hN : 1 ≤ N) : Measurable (Function.uncurry
    (fun (x : MlpParam N mW n × MlpParam n mF 1) (A : MlpParam n mA n) => Bn x.1 A x.2)) := by
  have h : Measurable (fun p : (MlpParam N mW n × MlpParam n mF 1) × MlpParam n mA n =>
      (p.1.1, p.2, p.1.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have h3 := (measurable_Bn (mA := mA) (mF := mF) hN).comp h
  simp only [Function.comp_def] at h3
  exact h3

lemma measurable_sdn' (hN : 1 ≤ N) : Measurable (Function.uncurry
    (fun (x : MlpParam N mW n × MlpParam n mF 1) (A : MlpParam n mA n) => sdn x.1 A x.2)) := by
  have h : Measurable (fun p : (MlpParam N mW n × MlpParam n mF 1) × MlpParam n mA n =>
      (p.1.1, p.2, p.1.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have h3 := (measurable_sdn (mA := mA) (mF := mF) hN).comp h
  simp only [Function.comp_def] at h3
  exact h3

lemma measurable_Bn_A (hN : 1 ≤ N) (W : MlpParam N mW n) (F : MlpParam n mF 1) :
    Measurable fun A : MlpParam n mA n => Bn W A F := by
  have h : Measurable (fun A : MlpParam n mA n => (W, A, F)) :=
    measurable_const.prodMk (measurable_id.prodMk measurable_const)
  have h3 := (measurable_Bn (mA := mA) (mF := mF) hN).comp h
  simp only [Function.comp_def] at h3
  exact h3

lemma measurable_sdn_A (hN : 1 ≤ N) (W : MlpParam N mW n) (F : MlpParam n mF 1) :
    Measurable fun A : MlpParam n mA n => sdn W A F := by
  have h : Measurable (fun A : MlpParam n mA n => (W, A, F)) :=
    measurable_const.prodMk (measurable_id.prodMk measurable_const)
  have h3 := (measurable_sdn (mA := mA) (mF := mF) hN).comp h
  simp only [Function.comp_def] at h3
  exact h3

theorem measurableSet_sepEvent (hN : 1 ≤ N) :
    MeasurableSet (sepEvent (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)) :=
  measurableSet_sep _ _ (measurable_Bn' hN) (measurable_sdn' hN)

theorem measurable_Jall (hN : 1 ≤ N) :
    Measurable (Jall (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)) := by
  have pA : Measurable (fun t : (MlpParam N mW n × MlpParam n mF 1) × MlpParam n mA n ×
      MlpParam n mA n => (t.1.1, (t.2.1, t.1.2.1, t.1.2.2.1))) := by fun_prop
  have pA' : Measurable (fun t : (MlpParam N mW n × MlpParam n mF 1) × MlpParam n mA n ×
      MlpParam n mA n => (t.1.1, (t.2.2, t.1.2.1, t.1.2.2.1))) := by fun_prop
  unfold Jall Jn Dn Tn
  refine Measurable.sub ?_ ?_
  · refine measurable_const.mul ?_
    unfold normSq
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (((measurable_aVec hN i).comp pA).sub ((measurable_aVec hN i).comp pA')).pow_const 2
  · refine measurable_const.mul ?_
    simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (((measurable_covDiag hN i).comp pA).add ((measurable_covDiag hN i).comp pA')).const_mul _

end BstLean.Part131

open BstLean.Part131 in
#print axioms measurable_Bn
open BstLean.Part131 in
#print axioms measurable_sdn
open BstLean.Part131 in
#print axioms measurable_Jall
