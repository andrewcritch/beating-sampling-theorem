import BstLean.Part108Defs

/-!
# Part 108: the deterministic step, the nested form, the rearrangement

* `succParts108 : SuccParts108`
* `nested108 : Nested108`
* `rearr108 : Rearr108`

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part108

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

/-! ## Rearrangement -/

theorem rearr108 : Rearr108 := by
  intro α β γ δ _ _ _ _ μ₁ μ₂ μ₃ μ₄ _ _ _ _
  have h1 : MeasurePreserving
      (Prod.map (Prod.map (id : α → α) (Prod.swap : β × γ → γ × β)) (id : δ → δ))
      ((μ₁.prod (μ₂.prod μ₃)).prod μ₄) ((μ₁.prod (μ₃.prod μ₂)).prod μ₄) :=
    ((MeasurePreserving.id μ₁).prod Measure.measurePreserving_swap).prod (MeasurePreserving.id μ₄)
  have h2 : MeasurePreserving
      (Prod.map (MeasurableEquiv.prodAssoc (α := α) (β := γ) (γ := β)).symm (id : δ → δ))
      ((μ₁.prod (μ₃.prod μ₂)).prod μ₄) (((μ₁.prod μ₃).prod μ₂).prod μ₄) :=
    ((measurePreserving_prodAssoc μ₁ μ₃ μ₂).symm _).prod (MeasurePreserving.id μ₄)
  have h3 := measurePreserving_prodAssoc (μ₁.prod μ₃) μ₂ μ₄
  exact ((h3.comp h2).comp h1).map_eq

/-! ## The nested form -/

theorem nested108 : Nested108 := by
  intro α β _ _ μ ν _ _ E δ hE hδ hP
  set h : α → ℝ := fun a => ν.real {b | (a, b) ∈ E} with hh
  have hmE : Measurable (fun a => ν (Prod.mk a ⁻¹' E)) := measurable_measure_prodMk_left hE
  have hm : Measurable h := hmE.ennreal_toReal
  have h01 : ∀ a, 0 ≤ h a ∧ h a ≤ 1 := fun a => ⟨measureReal_nonneg, measureReal_le_one⟩
  have hbm : BM h := ⟨hm, 1, fun a => by rw [abs_of_nonneg (h01 a).1]; exact (h01 a).2⟩
  have hint : ∫ a, h a ∂μ = (μ.prod ν).real E := by
    rw [measureReal_def, Measure.prod_apply hE]
    exact integral_toReal hmE.aemeasurable (Filter.Eventually.of_forall fun a => measure_lt_top _ _)
  set G : Set α := {a | 1 - Real.sqrt δ ≤ h a} with hG
  have hGm : MeasurableSet G := measurableSet_le measurable_const hm
  have hs0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  rcases hs0.eq_or_lt with h0 | hpos
  · -- `δ = 0`
    have hd0 : δ = 0 := by
      have := Real.sqrt_eq_zero'.mp h0.symm
      linarith
    rw [← h0, sub_zero]
    have hI : ∫ a, (1 - h a) ∂μ = 0 := by
      rw [integral_sub (integrable_const _) (hbm.integrable μ), hint]
      simp only [integral_const, smul_eq_mul, mul_one, probReal_univ]
      have : (μ.prod ν).real E ≤ 1 := measureReal_le_one
      rw [hd0] at hP
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg (fun a => by have := (h01 a).2; simp; linarith)
      ((integrable_const _).sub (hbm.integrable μ))).mp hI
    have hnull : μ Gᶜ = 0 := by
      refine measure_mono_null ?_ hae
      intro a ha
      have ha : h a < 1 := by
        have : ¬ (1 - Real.sqrt δ ≤ h a) := ha
        rw [← h0, sub_zero] at this
        exact not_le.mp this
      intro h'
      have h'' : 1 - h a = 0 := h'
      linarith
    have h1 : μ G = 1 := (prob_compl_eq_zero_iff hGm).mp hnull
    rw [measureReal_def, h1]
    simp
  · have hpt : ∀ a, h a ≤ (1 - Real.sqrt δ) + Real.sqrt δ * G.indicator (1 : α → ℝ) a := by
      intro a
      by_cases ha : a ∈ G
      · simp only [Set.indicator_of_mem ha, Pi.one_apply]
        linarith [(h01 a).2]
      · simp only [Set.indicator_of_notMem ha]
        have : h a < 1 - Real.sqrt δ := not_le.mp ha
        linarith
    have hi2 : Integrable (fun a => (1 - Real.sqrt δ) + Real.sqrt δ * G.indicator (1 : α → ℝ) a) μ :=
      (integrable_const _).add (((integrable_const (1 : ℝ)).indicator hGm).const_mul _)
    have hmono := integral_mono (hbm.integrable μ) hi2 hpt
    have e1 : ∫ a, ((1 - Real.sqrt δ) + Real.sqrt δ * G.indicator (1 : α → ℝ) a) ∂μ =
        ∫ _a, (1 - Real.sqrt δ) ∂μ + ∫ a, Real.sqrt δ * G.indicator (1 : α → ℝ) a ∂μ :=
      integral_add (integrable_const _) (((integrable_const (1 : ℝ)).indicator hGm).const_mul _)
    rw [e1, integral_const_mul, integral_indicator_one hGm, hint] at hmono
    simp only [integral_const, smul_eq_mul, probReal_univ, one_mul] at hmono
    have hsq : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ
    have : Real.sqrt δ * (1 - Real.sqrt δ) ≤ Real.sqrt δ * μ.real G := by nlinarith
    exact le_of_mul_le_mul_left this hpos

/-! ## An abstract seminorm step -/

section abs

variable {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]

lemma cs_bm {h g : α → ℝ} (hh : BM h) (hg : BM g) :
    (∫ x, h x * g x ∂P) ^ 2 ≤ (∫ x, h x ^ 2 ∂P) * ∫ x, g x ^ 2 ∂P := by
  have key : ∀ t : ℝ, 0 ≤ (∫ x, h x ^ 2 ∂P) * (t * t) + (2 * ∫ x, h x * g x ∂P) * t +
      ∫ x, g x ^ 2 ∂P := by
    intro t
    have i1 := (hh.sq).integrable P
    have i2 := (hh.mul hg).integrable P
    have i3 := (hg.sq).integrable P
    have e : (∫ x, h x ^ 2 ∂P) * (t * t) + (2 * ∫ x, h x * g x ∂P) * t + ∫ x, g x ^ 2 ∂P =
        ∫ x, (t * h x + g x) ^ 2 ∂P := by
      have : ∀ x, (t * h x + g x) ^ 2 = t * t * h x ^ 2 + (2 * t) * (h x * g x) + g x ^ 2 :=
        fun x => by ring
      simp_rw [this]
      have ea : ∫ x, (t * t * h x ^ 2 + (2 * t) * (h x * g x) + g x ^ 2) ∂P =
          ∫ x, (t * t * h x ^ 2 + (2 * t) * (h x * g x)) ∂P + ∫ x, g x ^ 2 ∂P :=
        integral_add ((i1.const_mul _).add (i2.const_mul _)) i3
      have eb : ∫ x, (t * t * h x ^ 2 + (2 * t) * (h x * g x)) ∂P =
          ∫ x, t * t * h x ^ 2 ∂P + ∫ x, (2 * t) * (h x * g x) ∂P :=
        integral_add (i1.const_mul _) (i2.const_mul _)
      rw [ea, eb, integral_const_mul, integral_const_mul]
      ring
    rw [e]
    exact integral_nonneg fun x => sq_nonneg _
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

lemma sqrt_tri {h g : α → ℝ} (hh : BM h) (hg : BM g) :
    Real.sqrt (∫ x, (h x - g x) ^ 2 ∂P) ≤
      Real.sqrt (∫ x, h x ^ 2 ∂P) + Real.sqrt (∫ x, g x ^ 2 ∂P) := by
  have i1 := (hh.sq).integrable P
  have i2 := (hh.mul hg).integrable P
  have i3 := (hg.sq).integrable P
  have hA : 0 ≤ ∫ x, h x ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∫ x, g x ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
  have e : ∫ x, (h x - g x) ^ 2 ∂P =
      (∫ x, h x ^ 2 ∂P) - 2 * (∫ x, h x * g x ∂P) + ∫ x, g x ^ 2 ∂P := by
    have : ∀ x, (h x - g x) ^ 2 = h x ^ 2 - 2 * (h x * g x) + g x ^ 2 := fun x => by ring
    simp_rw [this]
    have ea : ∫ x, (h x ^ 2 - 2 * (h x * g x) + g x ^ 2) ∂P =
        ∫ x, (h x ^ 2 - 2 * (h x * g x)) ∂P + ∫ x, g x ^ 2 ∂P :=
      integral_add (i1.sub (i2.const_mul _)) i3
    have eb : ∫ x, (h x ^ 2 - 2 * (h x * g x)) ∂P =
        ∫ x, h x ^ 2 ∂P - ∫ x, 2 * (h x * g x) ∂P := integral_sub i1 (i2.const_mul _)
    rw [ea, eb, integral_const_mul]
  have hC : |∫ x, h x * g x ∂P| ≤
      Real.sqrt (∫ x, h x ^ 2 ∂P) * Real.sqrt (∫ x, g x ^ 2 ∂P) := by
    rw [← Real.sqrt_mul hA]
    exact Real.abs_le_sqrt (cs_bm P hh hg)
  rw [e, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [abs_le.mp hC, Real.sq_sqrt hA, Real.sq_sqrt hB]

lemma succ_abs {f f1 f2 : α → ℝ} (h1 : BM f1) (h2 : BM f2) (κ c0 : ℝ) (hκ : 0 ≤ κ)
    (hf : ∀ x, f x = κ * (c0 + f1 x + f2 x)) :
    ∫ x, f x ∂P = κ * (c0 + ∫ x, f1 x ∂P + ∫ x, f2 x ∂P) ∧
    κ * (Real.sqrt (∫ x, (f1 x - ∫ y, f1 y ∂P) ^ 2 ∂P) -
        Real.sqrt (∫ x, (f2 x - ∫ y, f2 y ∂P) ^ 2 ∂P)) ≤
      Real.sqrt (∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P) := by
  have hmean : ∫ x, f x ∂P = κ * (c0 + ∫ x, f1 x ∂P + ∫ x, f2 x ∂P) := by
    simp_rw [hf]
    have ea : ∫ x, (c0 + f1 x + f2 x) ∂P = ∫ x, (c0 + f1 x) ∂P + ∫ x, f2 x ∂P :=
      integral_add ((integrable_const _).add (h1.integrable P)) (h2.integrable P)
    have eb : ∫ x, (c0 + f1 x) ∂P = ∫ _x, c0 ∂P + ∫ x, f1 x ∂P :=
      integral_add (integrable_const _) (h1.integrable P)
    rw [integral_const_mul, ea, eb]
    simp
  refine ⟨hmean, ?_⟩
  set m1 := ∫ x, f1 x ∂P
  set m2 := ∫ x, f2 x ∂P
  have g1 : BM (fun x => f1 x - m1) := h1.sub (BM.const m1)
  have g2 : BM (fun x => f2 x - m2) := h2.sub (BM.const m2)
  have hs : BM (fun x => (f1 x - m1) + (f2 x - m2)) := g1.add g2
  have e : ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P =
      κ ^ 2 * ∫ x, ((f1 x - m1) + (f2 x - m2)) ^ 2 ∂P := by
    rw [hmean, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf]
    ring
  rw [e, Real.sqrt_mul (sq_nonneg κ), Real.sqrt_sq hκ]
  have t := sqrt_tri P hs g2
  have e2 : ∀ x, ((f1 x - m1) + (f2 x - m2) - (f2 x - m2)) ^ 2 = (f1 x - m1) ^ 2 :=
    fun x => by ring
  simp_rw [e2] at t
  have := mul_le_mul_of_nonneg_left t hκ
  nlinarith

end abs

/-! ## The deterministic step -/

lemma ball_bdd {n : ℕ} {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ) :
    ∃ M, ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 ≤ 1 → |φ x| ≤ M := by
  have hc : IsCompact {x : Fin n → ℝ | ∑ i, x i ^ 2 ≤ 1} := by
    refine IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun _ : Fin n => isCompact_Icc (a := (-1 : ℝ)) (b := 1)) ?_ ?_
    · exact isClosed_le (by fun_prop) continuous_const
    · intro x hx i _
      have h1 : x i ^ 2 ≤ 1 :=
        le_trans (Finset.single_le_sum (f := fun i => x i ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)) hx
      constructor <;> nlinarith
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn hφ.continuousOn
  exact ⟨M, fun x hx => by simpa using hM x hx⟩

lemma bm_u {N n d : ℕ} (W : CoefIdx N n d → ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ) :
    BM (fun u : Fin N → ℝ => φ (sphProj (bwEval W u))) := by
  obtain ⟨M, hM⟩ := ball_bdd hφ
  exact ⟨hφ.measurable.comp (measurable_muMap W), M,
    fun u => hM _ (BstLean.Part106.sphProj_sq_le _)⟩

theorem succParts108 : SuccParts108 := by
  intro N n dW dA dF k hd hN hk W τ ω A1 F ρ a b hρ ha hb hab c hc
  have := BstLean.Part29.uniformSphere_isProbability N hN
  set φ1 : (Fin n → ℝ) → ℝ := fun x => BstLean.Part107.qLin A1 (linF hd F) x with hφ1
  set ψ : (Fin n → ℝ) → ℝ := psi hd ρ A1 F with hψ
  set φ : (Fin n → ℝ) → ℝ := BstLean.Part106.phiAF (ρ⁻¹ • A1) (c • F) with hφd
  set c0 : ℝ := ρ * F (0, mono0 n dF) with hc0
  set κ : ℝ := c * ρ⁻¹ with hκd
  have hκ : 0 ≤ κ := mul_nonneg hc (inv_nonneg.mpr hρ.le)
  have hpt : ∀ x, φ x = κ * (c0 + φ1 x + ψ x) := by
    intro x
    simp only [hφd, hφ1, hψ, hc0, hκd, BstLean.Part106.phiAF, psi, Htail, BstLean.Part107.qLin,
      dot, linF, BstLean.Part106.bwEval_smul, Pi.smul_apply, smul_eq_mul]
    have hne : ρ ≠ 0 := hρ.ne'
    have e : ∑ i, F (0, mono1 n dF hd i) * (ρ⁻¹ * bwEval A1 x i) =
        ρ⁻¹ * ∑ i, F (0, mono1 n dF hd i) * bwEval A1 x i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    field_simp
    ring
  have hb1 := BstLean.Part106.continuous_bwEval A1
  have cφ1 : Continuous φ1 := by
    simp only [hφ1, BstLean.Part107.qLin, dot]
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((continuous_apply i).comp hb1)
  have cH : Continuous (Htail hd F) := by
    unfold Htail
    exact (((continuous_apply 0).comp (BstLean.Part106.continuous_bwEval F)).sub
      continuous_const).sub
      (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))
  have cψ : Continuous ψ := by
    simp only [hψ]
    unfold psi
    exact continuous_const.mul (cH.comp (hb1.const_smul ρ⁻¹ : Continuous fun x => ρ⁻¹ • bwEval A1 x))
  have B1 := bm_u W cφ1
  have B2 := bm_u W cψ
  obtain ⟨hmean, hsd⟩ := succ_abs (uniformSphere N) B1 B2 κ c0 hκ
    (f := fun u => φ (sphProj (bwEval W u))) (fun u => hpt _)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hg : BstLean.Part106.gVal W τ φ ω =
      κ * (c0 + BstLean.Part106.gVal W τ φ1 ω + BstLean.Part106.gVal W τ ψ ω) := by
    unfold BstLean.Part106.gVal
    simp_rw [hpt]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  unfold Succ Err Vu Bu at *
  rw [hg, hmean]
  rw [hmean] at hsd
  set E1 := BstLean.Part106.gVal W τ φ1 ω - ∫ u, φ1 (sphProj (bwEval W u)) ∂uniformSphere N
  set E2 := BstLean.Part106.gVal W τ ψ ω - ∫ u, ψ (sphProj (bwEval W u)) ∂uniformSphere N
  set S1 := Real.sqrt (∫ u, (φ1 (sphProj (bwEval W u)) -
    ∫ u, φ1 (sphProj (bwEval W u)) ∂uniformSphere N) ^ 2 ∂uniformSphere N)
  set S2 := Real.sqrt (∫ u, (ψ (sphProj (bwEval W u)) -
    ∫ u, ψ (sphProj (bwEval W u)) ∂uniformSphere N) ^ 2 ∂uniformSphere N)
  have e : κ * (c0 + BstLean.Part106.gVal W τ φ1 ω + BstLean.Part106.gVal W τ ψ ω) -
      κ * (c0 + ∫ u, φ1 (sphProj (bwEval W u)) ∂uniformSphere N +
        ∫ u, ψ (sphProj (bwEval W u)) ∂uniformSphere N) = κ * (E1 + E2) := by
    simp only [E1, E2]; ring
  rw [e, abs_mul, abs_of_nonneg hκ]
  have h3 : |E1 + E2| ≤ 1 / 2 * (S1 - S2) := by
    have := abs_add_le E1 E2
    linarith
  calc κ * |E1 + E2| ≤ κ * (1 / 2 * (S1 - S2)) := mul_le_mul_of_nonneg_left h3 hκ
    _ = 1 / 2 * (κ * (S1 - S2)) := by ring
    _ ≤ _ := by linarith

end BstLean.Part108

#print axioms BstLean.Part108.succParts108
#print axioms BstLean.Part108.nested108
#print axioms BstLean.Part108.rearr108
