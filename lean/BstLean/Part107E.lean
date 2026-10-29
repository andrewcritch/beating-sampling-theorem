import BstLean.Part107Eb

/-!
# Part 107 (item 5): Lemma E for the linear part

* `lemmaE107 (hQ : QDom107) : LemmaE107`.
* `lam8_107 : Lam8_107` is in `Part107Ea.lean`.

The proof applies `lemmaE_fixed` (`Part107Eb.lean`) to the bounded function
`cubePhi (A, ℓ) x = ℓ·A(x)` on the cube `|x_i| ≤ 1` (and `0` off the cube), for each `(A, ℓ)`, and
integrates over `(A, ℓ)`.
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

variable {N n dW dA k : ℕ}

lemma abs_sphProj_le (y : Fin n → ℝ) (i : Fin n) : |sphProj y i| ≤ 1 := by
  unfold sphProj
  simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : y i ^ 2 ≤ ∑ j, y j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
  have h2 : |y i| ≤ Real.sqrt (∑ j, y j ^ 2) := Real.abs_le_sqrt h1
  rw [abs_mul, abs_of_nonneg (by positivity), one_div, inv_mul_eq_div]
  exact div_le_one_of_le₀ h2 (Real.sqrt_nonneg _)

/-- `ℓ·A(x)` on the cube `|x_i| ≤ 1`, and `0` off the cube. -/
noncomputable def cubePhi (al : (CoefIdx n n dA → ℝ) × (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  if ∀ i, |x i| ≤ 1 then qLin al.1 al.2 x else 0

lemma measurable_qLin3 : Measurable
    (fun p : ((CoefIdx n n dA → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) => qLin p.1.1 p.1.2 p.2) := by
  unfold qLin
  exact measurable_dot2.comp ((measurable_snd.comp measurable_fst).prodMk
    (measurable_bwEval_comp (measurable_fst.comp measurable_fst) measurable_snd))

lemma e_measurable_qLin (A : CoefIdx n n dA → ℝ) (ℓ : Fin n → ℝ) :
    Measurable (fun x : Fin n → ℝ => qLin A ℓ x) :=
  measurable_qLin3.comp
    (measurable_const.prodMk measurable_id : Measurable fun x : Fin n → ℝ => ((A, ℓ), x))

lemma measurable_cubePhi2 : Measurable
    (fun p : ((CoefIdx n n dA → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) => cubePhi p.1 p.2) := by
  unfold cubePhi
  refine Measurable.ite ?_ measurable_qLin3 measurable_const
  have : {p : ((CoefIdx n n dA → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) | ∀ i, |p.2 i| ≤ 1} =
      ⋂ i, {p | |p.2 i| ≤ 1} := by
    ext p; simp
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_le
    (((measurable_pi_apply i).comp measurable_snd).abs) measurable_const

lemma measurable_cubePhi (al : (CoefIdx n n dA → ℝ) × (Fin n → ℝ)) : Measurable (cubePhi al) :=
  measurable_cubePhi2.comp
    (measurable_const.prodMk measurable_id : Measurable fun x : Fin n → ℝ => (al, x))

lemma cubePhi_sph (al : (CoefIdx n n dA → ℝ) × (Fin n → ℝ)) (y : Fin n → ℝ) :
    cubePhi al (sphProj y) = qLin al.1 al.2 (sphProj y) :=
  by simp [cubePhi, abs_sphProj_le]

lemma cubePhi_bound {al : (CoefIdx n n dA → ℝ) × (Fin n → ℝ)} {q : ℝ} (hq : 0 ≤ q)
    (hb : ∀ x : Fin n → ℝ, (∀ i, |x i| ≤ 1) → |qLin al.1 al.2 x| ≤ q) (x : Fin n → ℝ) :
    |cubePhi al x| ≤ q := by
  unfold cubePhi
  split_ifs with h
  · exact hb x h
  · simpa using hq

lemma abs_integral_le_const {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {F : α → ℝ} {C : ℝ} (hb : ∀ x, |F x| ≤ C) : |∫ x, F x ∂μ| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := C)
    (Filter.Eventually.of_forall fun x => by simpa using hb x)
  simpa using h

lemma measurable_standIn2 (τ : ℝ) :
    Measurable (fun p : (CoefIdx N n dW → ℝ) × Prim N n => standIn p.1 τ p.2) := by
  unfold standIn
  have h1 : Measurable (fun p : (CoefIdx N n dW → ℝ) × Prim N n => bwEval (mixW p.1 0) p.2.1) :=
    measurable_bwEval_comp ((measurable_mixW_left 0).comp measurable_fst)
      (measurable_fst.comp measurable_snd)
  have h2 : Measurable (fun p : (CoefIdx N n dW → ℝ) × Prim N n => τ • p.2.2) :=
    (measurable_snd.comp measurable_snd).const_smul τ
  exact measurable_sphProj.comp (h1.add h2)

section eqs

variable (hN : 1 ≤ N)

lemma Bmean_eq (W : CoefIdx N n dW → ℝ) (al : (CoefIdx n n dA → ℝ) × (Fin n → ℝ)) :
    Bmean W al.1 al.2 = ∫ u, cubePhi al (sphProj (bwEval W u)) ∂uniformSphere N := by
  unfold Bmean muW
  rw [integral_map (measurable_muMap W).aemeasurable
    (e_measurable_qLin al.1 al.2).aestronglyMeasurable]
  simp only [cubePhi_sph]

lemma muInt_eq (W : CoefIdx N n dW → ℝ) (al : (CoefIdx n n dA → ℝ) × (Fin n → ℝ)) :
    ∫ x, cubePhi al x ∂muW W = ∫ u, cubePhi al (sphProj (bwEval W u)) ∂uniformSphere N := by
  unfold muW
  rw [integral_map (measurable_muMap W).aemeasurable (measurable_cubePhi al).aestronglyMeasurable]

lemma muInt2_eq (W : CoefIdx N n dW → ℝ) (al : (CoefIdx n n dA → ℝ) × (Fin n → ℝ)) :
    ∫ x, cubePhi al x ^ 2 ∂muW W =
      ∫ u, cubePhi al (sphProj (bwEval W u)) ^ 2 ∂uniformSphere N := by
  unfold muW
  rw [integral_map (measurable_muMap W).aemeasurable
    ((measurable_cubePhi al).pow_const 2).aestronglyMeasurable]

lemma e_X1_eq (W : CoefIdx N n dW → ℝ) (al : (CoefIdx n n dA → ℝ) × (Fin n → ℝ)) :
    X1 W al.1 al.2 = Var[cubePhi al; muW W] := by
  unfold X1 muW
  rw [variance_map (e_measurable_qLin al.1 al.2).aemeasurable (measurable_muMap W).aemeasurable,
    variance_map (measurable_cubePhi al).aemeasurable (measurable_muMap W).aemeasurable]
  congr 1
  funext u
  simp only [Function.comp, cubePhi_sph]

lemma gErr_eq (σ : ℝ) (W : CoefIdx N n dW → ℝ) (al : (CoefIdx n n dA → ℝ) × (Fin n → ℝ))
    (s : Fin k → Prim N n) :
    gErr σ ((W, al), s) = (1 / (k : ℝ)) * ∑ i, cubePhi al (standIn W (tauOf dW σ) (s i)) -
      ∫ x, cubePhi al x ∂muW W := by
  unfold gErr gProg
  rw [muInt_eq, ← Bmean_eq]
  simp only [standIn, cubePhi_sph]

include hN in
lemma measurable_Bm : Measurable
    (fun p : (CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ)) =>
      ∫ u, cubePhi p.2 (sphProj (bwEval p.1 u)) ∂uniformSphere N) := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have h : Measurable (fun q : ((CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) ×
      (Fin N → ℝ) => cubePhi q.1.2 (sphProj (bwEval q.1.1 q.2))) :=
    measurable_cubePhi2.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_sphProj.comp
        (measurable_bwEval_comp (measurable_fst.comp measurable_fst) measurable_snd)))
  exact (h.stronglyMeasurable.integral_prod_right').measurable

include hN in
lemma measurable_Bm2 : Measurable
    (fun p : (CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ)) =>
      ∫ u, cubePhi p.2 (sphProj (bwEval p.1 u)) ^ 2 ∂uniformSphere N) := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have h : Measurable (fun q : ((CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) ×
      (Fin N → ℝ) => cubePhi q.1.2 (sphProj (bwEval q.1.1 q.2)) ^ 2) :=
    (measurable_cubePhi2.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_sphProj.comp
        (measurable_bwEval_comp (measurable_fst.comp measurable_fst) measurable_snd)))).pow_const 2
  exact (h.stronglyMeasurable.integral_prod_right').measurable

include hN in
lemma measurable_gErr (σ : ℝ) : Measurable
    (fun ω : ((CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) ×
      (Fin k → Prim N n) => gErr σ ω) := by
  have e : (fun ω : ((CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) ×
      (Fin k → Prim N n) => gErr σ ω) = fun ω =>
        (1 / (k : ℝ)) * ∑ i, cubePhi ω.1.2 (standIn ω.1.1 (tauOf dW σ) (ω.2 i)) -
          ∫ u, cubePhi ω.1.2 (sphProj (bwEval ω.1.1 u)) ∂uniformSphere N := by
    funext ω
    obtain ⟨⟨W, al⟩, s⟩ := ω
    rw [gErr_eq, muInt_eq]
  rw [e]
  have h1 : ∀ i : Fin k, Measurable (fun ω : ((CoefIdx N n dW → ℝ) ×
      ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) × (Fin k → Prim N n) =>
      standIn ω.1.1 (tauOf dW σ) (ω.2 i)) := by
    intro i
    have hf : Measurable (fun ω : ((CoefIdx N n dW → ℝ) ×
        ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) × (Fin k → Prim N n) =>
        ((ω.1.1, ω.2 i) : (CoefIdx N n dW → ℝ) × Prim N n)) :=
      (measurable_fst.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)
    exact Measurable.comp
      (g := fun p : (CoefIdx N n dW → ℝ) × Prim N n => standIn p.1 (tauOf dW σ) p.2)
      (f := fun ω : ((CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) ×
        (Fin k → Prim N n) => ((ω.1.1, ω.2 i) : (CoefIdx N n dW → ℝ) × Prim N n))
      (measurable_standIn2 (tauOf dW σ)) hf
  have h2 : ∀ i : Fin k, Measurable (fun ω : ((CoefIdx N n dW → ℝ) ×
      ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) × (Fin k → Prim N n) =>
      cubePhi ω.1.2 (standIn ω.1.1 (tauOf dW σ) (ω.2 i))) := fun i =>
    measurable_cubePhi2.comp ((measurable_snd.comp measurable_fst).prodMk (h1 i))
  have h3 : Measurable (fun ω : ((CoefIdx N n dW → ℝ) ×
      ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) × (Fin k → Prim N n) =>
      ∑ i, cubePhi ω.1.2 (standIn ω.1.1 (tauOf dW σ) (ω.2 i))) :=
    Finset.measurable_sum _ fun i _ => h2 i
  have h4 : Measurable (fun ω : ((CoefIdx N n dW → ℝ) ×
      ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) × (Fin k → Prim N n) =>
      ∫ u, cubePhi ω.1.2 (sphProj (bwEval ω.1.1 u)) ∂uniformSphere N) :=
    (measurable_Bm hN).comp measurable_fst
  exact (h3.const_mul _).sub h4

end eqs

/-- **Lemma E for the linear part**, given the dominating function `QDom107`. -/
theorem lemmaE107 (hQ : QDom107) : LemmaE107 := by
  intro N n dW dA k σ hN hd hk
  have := BstLean.Part29.uniformSphere_isProbability N hN
  obtain ⟨Q, hQm, hQ0, hQ4, hQb⟩ := hQ n dA
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hφQ : ∀ (al : (CoefIdx n n dA → ℝ) × (Fin n → ℝ)) (x : Fin n → ℝ),
      |cubePhi al x| ≤ Q al := fun al x => cubePhi_bound (hQ0 al) (hQb al) x
  have bφ : ∀ al : (CoefIdx n n dA → ℝ) × (Fin n → ℝ), BM (cubePhi al) := fun al =>
    ⟨measurable_cubePhi al, Q al, hφQ al⟩
  have hQ2 : Integrable (fun al => Q al ^ 2) (AL n dA) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hQ4)
      (hQm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun al => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (Q al ^ 2 - 1)]
  -- the bound of the error
  have hgb : ∀ ω : ((CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) ×
      (Fin k → Prim N n), gErr σ ω ^ 2 ≤ 4 * Q ω.1.2 ^ 2 := by
    rintro ⟨⟨W, al⟩, s⟩
    rw [gErr_eq]
    have := muW_prob hN W
    have h1 : |∫ x, cubePhi al x ∂muW W| ≤ Q al := abs_integral_le_const _ (hφQ al)
    have h2 : |(1 / (k : ℝ)) * ∑ i, cubePhi al (standIn W (tauOf dW σ) (s i))| ≤ Q al := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have : |∑ i, cubePhi al (standIn W (tauOf dW σ) (s i))| ≤ (k : ℝ) * Q al := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => hφQ al _).trans ?_
        simp
      calc 1 / (k : ℝ) * |∑ i, cubePhi al (standIn W (tauOf dW σ) (s i))|
          ≤ 1 / (k : ℝ) * ((k : ℝ) * Q al) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = Q al := by field_simp
    have h3 := abs_le.1 h1
    have h4 := abs_le.1 h2
    have h5 : |(1 / (k : ℝ)) * ∑ i, cubePhi al (standIn W (tauOf dW σ) (s i)) -
        ∫ x, cubePhi al x ∂muW W| ≤ 2 * Q al := by
      rw [abs_le]; constructor <;> linarith
    calc _ = |(1 / (k : ℝ)) * ∑ i, cubePhi al (standIn W (tauOf dW σ) (s i)) -
          ∫ x, cubePhi al x ∂muW W| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * Q al) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h5 2
      _ = 4 * Q al ^ 2 := by ring
  have hInt : Integrable (fun ω => gErr (N := N) (n := n) (dW := dW) (dA := dA) (k := k) σ ω ^ 2)
      (Full N n dW dA k σ) := by
    have hdom : Integrable (fun ω : ((CoefIdx N n dW → ℝ) ×
        ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) × (Fin k → Prim N n) => 4 * Q ω.1.2 ^ 2)
        (Full N n dW dA k σ) :=
      (((hQ2.const_mul 4).comp_snd (bwGauss N n dW σ)).comp_fst
        (Measure.pi fun _ : Fin k => primM N n))
    refine Integrable.mono' hdom ((measurable_gErr hN σ).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hgb ω
  -- the spread
  have hX1e : ∀ p : (CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ)),
      X1 p.1 p.2.1 p.2.2 = ∫ u, cubePhi p.2 (sphProj (bwEval p.1 u)) ^ 2 ∂uniformSphere N -
        (∫ u, cubePhi p.2 (sphProj (bwEval p.1 u)) ∂uniformSphere N) ^ 2 := by
    rintro ⟨W, al⟩
    have := muW_prob hN W
    rw [e_X1_eq, bm_var (bφ al), muInt_eq, muInt2_eq]
  have hX1b : ∀ p : (CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ)),
      |X1 p.1 p.2.1 p.2.2| ≤ Q p.2 ^ 2 := by
    rintro ⟨W, al⟩
    have := muW_prob hN W
    rw [e_X1_eq, abs_of_nonneg (variance_nonneg _ _), bm_var (bφ al)]
    have h1 : ∫ x, cubePhi al x ^ 2 ∂muW W ≤ Q al ^ 2 := by
      have := abs_integral_le_const (muW W) (F := fun x => cubePhi al x ^ 2) (C := Q al ^ 2)
        (fun x => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hφQ al x) 2)
      exact (le_abs_self _).trans this
    nlinarith [sq_nonneg (∫ x, cubePhi al x ∂muW W)]
  have hX1Int : Integrable (fun p : (CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ)) =>
      X1 p.1 p.2.1 p.2.2) (PP N n dW dA σ) := by
    have hm : Measurable (fun p : (CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ)) =>
        X1 p.1 p.2.1 p.2.2) := by
      simp_rw [hX1e]
      exact (measurable_Bm2 hN).sub ((measurable_Bm hN).pow_const 2)
    refine Integrable.mono' (hQ2.comp_snd (bwGauss N n dW σ)) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact hX1b p
  refine ⟨hInt, ?_⟩
  have e1 : ∫ ω, gErr (N := N) (n := n) (dW := dW) (dA := dA) (k := k) σ ω ^ 2
      ∂Full N n dW dA k σ =
      ∫ al, ∫ W, ∫ s, gErr (N := N) (n := n) (dW := dW) (dA := dA) (k := k) σ ((W, al), s) ^ 2
        ∂(Measure.pi fun _ : Fin k => primM N n) ∂bwGauss N n dW σ ∂AL n dA := by
    rw [integral_prod _ hInt, integral_prod_symm _ hInt.integral_prod_left]
  have e2 : ∫ ω, X1 ω.1 ω.2.1 ω.2.2 ∂PP N n dW dA σ =
      ∫ al, ∫ W, X1 W al.1 al.2 ∂bwGauss N n dW σ ∂AL n dA := integral_prod_symm _ hX1Int
  rw [e1, e2, ← integral_const_mul, ← integral_const_mul]
  refine integral_mono (hInt.integral_prod_left.integral_prod_right.const_mul _)
    (hX1Int.integral_prod_right.const_mul _) fun al => ?_
  have h := lemmaE_fixed hN hd σ (bφ al) k hk
  simp only [gErr_eq, e_X1_eq]
  exact h

#print axioms lemmaE107
#print axioms lam8_107

end BstLean.Part107
