import BstLean.Part170Meas

/-!
# Part 170 (file `Ev`): the bias event and its Markov charge

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, formula `t7:p08:charge` ("Fubini at each node and Markov give the
charges"). The paper uses four events (fluctuation and bias, location and energy, orders
24, 8, 16, 8). Lean uses two events, one for the whole exact-rule error of each pass, both of
order 8; this is allowed by the room at `n ≥ 80 000` (see the report).

* `windowW wr`: the World window `τ₀ > 0`, `0.46 ≤ θ ≤ 0.55` as a property of the retained World
  data.
* `intF c = ∫_a (exF c a)⁸ dμ_I`, `intW c` (over ALL indices; the kept set is a subset).
* `SB Gs A_f A_ω`: the pairs `(wr, θ)` such that, if `wr` is in the window, then `(wr, θ) ∈ Gs`,
  `intF ≤ A_f⁸` and `intW ≤ A_ω⁸`. **`Ebias Gs A_f A_ω = {c | (c.1, (A₁, A₂)) ∈ SB}`.**
  `Gs` is a free measurable family of Agent events (for example operator or statistics
  events) on which the moment bounds are proved.
* `NodeMom Gs F E`: for every World datum in the window and every node `g < J_s`,
  `∫_{θ ∈ Gs} (exFn g)⁸ dν_A ≤ F⁸` and `∫_{θ ∈ Gs} (exWn g)⁸ dν_A ≤ E⁸` (moment bounds over the
  Agent hidden matrices at a fixed node).
* **`retDist_pair_charge`**: a family of events of `(A₁, A₂)` indexed by the retained World
  data, each with complement probability at most `δ`, gives an event of the retained data with
  complement probability at most `δ`.
* **`world_charge`**: Markov and Tonelli at a fixed World datum:
  `ν_A{θ : (wr, θ) ∉ SB} ≤ δ_G + (F/A_f)⁸ + (E/A_ω)⁸`.
* **`Ebias_charge`**: `Pr(Ebiasᶜ) ≤ δ_G + (F/A_f)⁸ + (E/A_ω)⁸`.
-/

namespace BstLean.Part170

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part153 (nuA)
open BstLean.Part150 (thetaC)

variable {n : ℕ}

/-- The World window as a property of the retained World data. -/
def windowW (wr : WRet n) : Prop :=
  0 < tau0p wr.1 ∧ 46 / 100 ≤ thetaC wr.2 (tau0p wr.1) ∧ thetaC wr.2 (tau0p wr.1) ≤ 55 / 100

lemma measurableSet_windowW : MeasurableSet {wr : WRet n | windowW wr} := by
  have ht : Measurable (fun wr : WRet n => tau0p wr.1) := measurable_tau0p.comp measurable_fst
  have hθ : Measurable (fun wr : WRet n => thetaC wr.2 (tau0p wr.1)) := by
    unfold thetaC
    exact ((ht.pow_const 2).const_mul _).div
      (((BstLean.Part150.measurable_rhoC (n := n)).comp (measurable_snd.prodMk ht)).pow_const 2)
  exact (measurableSet_lt measurable_const ht).inter
    ((measurableSet_le measurable_const hθ).inter (measurableSet_le hθ measurable_const))

/-- `intF c = ∫_a (exF c a)⁸ dμ_I`. -/
noncomputable def intF (c : Ret n) : ℝ := ∫ a, exF c a ^ 8 ∂muI n

/-- `intW c = ∫_a (exW c a)⁸ dμ_I`. -/
noncomputable def intW (c : Ret n) : ℝ := ∫ a, exW c a ^ 8 ∂muI n

lemma measurable_intF_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} (hC : Measurable C) :
    Measurable (fun x => intF (C x)) := by
  unfold intF
  have h : Measurable (fun p : β × Ix n => exF (C p.1) p.2 ^ 8) :=
    (measurable_exF_joint (hC.comp measurable_fst) measurable_snd).pow_const 8
  exact (h.stronglyMeasurable.integral_prod_right' (ν := muI n)).measurable

lemma measurable_intW_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} (hC : Measurable C) :
    Measurable (fun x => intW (C x)) := by
  unfold intW
  have h : Measurable (fun p : β × Ix n => exW (C p.1) p.2 ^ 8) :=
    (measurable_exW_joint (hC.comp measurable_fst) measurable_snd).pow_const 8
  exact (h.stronglyMeasurable.integral_prod_right' (ν := muI n)).measurable

/-- The pairs `(wr, θ)` of the bias event. -/
def SB (Gs : Set (WRet n × AHid n)) (Af Aw : ℝ) : Set (WRet n × AHid n) :=
  {p | windowW p.1 → p ∈ Gs ∧ intF (mkR p.1 p.2) ≤ Af ^ 8 ∧ intW (mkR p.1 p.2) ≤ Aw ^ 8}

lemma measurableSet_SB {Gs : Set (WRet n × AHid n)} (hG : MeasurableSet Gs) (Af Aw : ℝ) :
    MeasurableSet (SB Gs Af Aw) := by
  have hw : MeasurableSet {p : WRet n × AHid n | windowW p.1} :=
    measurable_fst measurableSet_windowW
  have h1 : MeasurableSet {p : WRet n × AHid n | intF (mkR p.1 p.2) ≤ Af ^ 8} :=
    measurableSet_le (measurable_intF_comp measurable_mkR) measurable_const
  have h2 : MeasurableSet {p : WRet n × AHid n | intW (mkR p.1 p.2) ≤ Aw ^ 8} :=
    measurableSet_le (measurable_intW_comp measurable_mkR) measurable_const
  have e : SB Gs Af Aw = {p : WRet n × AHid n | windowW p.1}ᶜ ∪ (Gs ∩ ({p : WRet n × AHid n |
      intF (mkR p.1 p.2) ≤ Af ^ 8} ∩ {p : WRet n × AHid n | intW (mkR p.1 p.2) ≤ Aw ^ 8})) := by
    ext p
    simp only [SB, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
    tauto
  rw [e]
  exact hw.compl.union (hG.inter (h1.inter h2))

/-- **The bias event.** -/
def Ebias (Gs : Set (WRet n × AHid n)) (Af Aw : ℝ) : Set (Ret n) :=
  {c | (c.1, c.2.1.1) ∈ SB Gs Af Aw}

lemma measurableSet_Ebias {Gs : Set (WRet n × AHid n)} (hG : MeasurableSet Gs) (Af Aw : ℝ) :
    MeasurableSet (Ebias Gs Af Aw) :=
  (measurable_fst.prodMk (measurable_fst.comp (measurable_fst.comp measurable_snd)))
    (measurableSet_SB hG Af Aw)

/-! ## The charge of a family of Agent events indexed by the retained World data -/

/-- **The charge of a family of Agent events indexed by the World data.** -/
theorem retDist_pair_charge (D : Centres n) {S : Set (WRet n × AHid n)} (hS : MeasurableSet S)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ wr : WRet n, (nuA n).real {θ | (wr, θ) ∉ S} ≤ δ) :
    (retDist D).real {c : Ret n | (c.1, c.2.1.1) ∉ S} ≤ δ := by
  have hT : MeasurableSet {c : Ret n | (c.1, c.2.1.1) ∉ S} :=
    ((measurable_fst.prodMk (measurable_fst.comp (measurable_fst.comp measurable_snd))) hS).compl
  have mr := measurable_retVal D
  rw [← noise_retVal D, map_measureReal_apply mr hT]
  have hP := mr hT
  have key : (noiseC n) (retVal D ⁻¹' {c : Ret n | (c.1, c.2.1.1) ∉ S}) ≤ ENNReal.ofReal δ := by
    unfold noiseC
    rw [Measure.prod_apply hP]
    have hb : ∀ w : WRet n, ((cAm n).prod (mlpGauss n (mF n) 1))
        (Prod.mk w ⁻¹' (retVal D ⁻¹' {c : Ret n | (c.1, c.2.1.1) ∉ S})) ≤ ENNReal.ofReal δ := by
      intro w
      have hB : MeasurableSet {θ : AHid n | (retValW D w, θ) ∉ S} :=
        (measurable_prodMk_left hS).compl
      have e : (Prod.mk w ⁻¹' (retVal D ⁻¹' {c : Ret n | (c.1, c.2.1.1) ∉ S})) =
          (fun y : ARet n × FPar n => y.1.1) ⁻¹' {θ : AHid n | (retValW D w, θ) ∉ S} := by
        ext y
        rfl
      have h0 : ((cAm n).prod (mlpGauss n (mF n) 1))
          ((fun y : ARet n × FPar n => y.1.1) ⁻¹' {θ : AHid n | (retValW D w, θ) ∉ S}) =
          (hidGauss n (mA n)) {θ : AHid n | (retValW D w, θ) ∉ S} := by
        rw [← BstLean.Part160.map_agentHid]
        exact (Measure.map_apply (show Measurable (fun y : ARet n × FPar n => y.1.1) from
          measurable_fst.comp measurable_fst) hB).symm
      rw [e, h0]
      have h := hδ (retValW D w)
      have h2 : (hidGauss n (mA n)) {θ : AHid n | (retValW D w, θ) ∉ S} =
          ENNReal.ofReal ((nuA n).real {θ | (retValW D w, θ) ∉ S}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      rw [h2]
      exact ENNReal.ofReal_le_ofReal h
    calc ∫⁻ w, ((cAm n).prod (mlpGauss n (mF n) 1))
          (Prod.mk w ⁻¹' (retVal D ⁻¹' {c : Ret n | (c.1, c.2.1.1) ∉ S})) ∂cWm n
        ≤ ∫⁻ _w, ENNReal.ofReal δ ∂cWm n := lintegral_mono hb
      _ = ENNReal.ofReal δ := by rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.toReal_le_of_le_ofReal hδ0 key

/-! ## Markov and Tonelli at a fixed World datum -/

/-- **Markov after Tonelli.** If `X θ a` is jointly measurable, bounded in `a` for each `θ`, and
`∫_{θ ∈ G} X(θ, a)⁸ dν_A ≤ F⁸` for every index `a`, then
`ν_A{θ ∈ G : A⁸ < ∫_a X(θ, a)⁸ dμ_I} ≤ (F/A)⁸`. -/
theorem markov_tonelli {X : AHid n → Ix n → ℝ} (hX : Measurable (fun p : AHid n × Ix n => X p.1 p.2))
    (hb : ∀ θ, ∃ M, ∀ a, |X θ a| ≤ M) {G : Set (AHid n)} (hG : MeasurableSet G) {F A : ℝ}
    (hA : 0 < A) (hF : ∀ a, ∫⁻ θ in G, ENNReal.ofReal (X θ a ^ 8) ∂nuA n ≤ ENNReal.ofReal (F ^ 8)) :
    nuA n {θ | θ ∈ G ∧ A ^ 8 < ∫ a, X θ a ^ 8 ∂muI n} ≤ ENNReal.ofReal ((F / A) ^ 8) := by
  have hint : ∀ θ, Integrable (fun a => X θ a ^ 8) (muI n) := by
    intro θ
    obtain ⟨M, hM⟩ := hb θ
    refine Integrable.mono' (integrable_const (M ^ 8))
      ((hX.comp (measurable_const.prodMk measurable_id)).pow_const 8).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM a) 8
  have hof : ∀ θ, ENNReal.ofReal (∫ a, X θ a ^ 8 ∂muI n) =
      ∫⁻ a, ENNReal.ofReal (X θ a ^ 8) ∂muI n := fun θ =>
    ofReal_integral_eq_lintegral_ofReal (hint θ)
      (Filter.Eventually.of_forall fun a => by positivity)
  set f : AHid n → ENNReal := G.indicator (fun θ => ENNReal.ofReal (∫ a, X θ a ^ 8 ∂muI n))
  have mΦ : Measurable (fun θ => ∫ a, X θ a ^ 8 ∂muI n) :=
    ((hX.pow_const 8).stronglyMeasurable.integral_prod_right' (ν := muI n)).measurable
  have mf : Measurable f := (ENNReal.measurable_ofReal.comp mΦ).indicator hG
  have hsub : {θ | θ ∈ G ∧ A ^ 8 < ∫ a, X θ a ^ 8 ∂muI n} ⊆
      {θ | ENNReal.ofReal (A ^ 8) ≤ f θ} := by
    intro θ ⟨hθ, hlt⟩
    show ENNReal.ofReal (A ^ 8) ≤ f θ
    simp only [f, Set.indicator_of_mem hθ]
    exact ENNReal.ofReal_le_ofReal hlt.le
  have hA8 : ENNReal.ofReal (A ^ 8) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div mf.aemeasurable hA8
    ENNReal.ofReal_ne_top).trans ?_)
  have hlin : ∫⁻ θ, f θ ∂nuA n ≤ ENNReal.ofReal (F ^ 8) := by
    simp only [f]
    rw [lintegral_indicator hG]
    simp_rw [hof]
    have mU : Measurable (Function.uncurry fun θ a => ENNReal.ofReal (X θ a ^ 8)) :=
      ENNReal.measurable_ofReal.comp (hX.pow_const 8)
    rw [lintegral_lintegral_swap mU.aemeasurable]
    calc ∫⁻ a, ∫⁻ θ in G, ENNReal.ofReal (X θ a ^ 8) ∂nuA n ∂muI n
        ≤ ∫⁻ _a, ENNReal.ofReal (F ^ 8) ∂muI n := lintegral_mono hF
      _ = ENNReal.ofReal (F ^ 8) := by rw [lintegral_const, measure_univ, mul_one]
  calc (∫⁻ θ, f θ ∂nuA n) / ENNReal.ofReal (A ^ 8)
      ≤ ENNReal.ofReal (F ^ 8) / ENNReal.ofReal (A ^ 8) := by gcongr
    _ = ENNReal.ofReal ((F / A) ^ 8) := by
      rw [div_pow, ENNReal.ofReal_div_of_pos (by positivity)]

/-- The node of the index `a` for the World data `wr` (it does not read `θ`). -/
noncomputable def gW (wr : WRet n) (a : Ix n) : ℕ :=
  gIdx (mkR wr 0) (latC (paperDesignP n) (mkR wr 0) a)

lemma exF_mkR_node (wr : WRet n) (θ : AHid n) (a : Ix n) :
    exF (mkR wr θ) a = exFn (mkR wr θ) (gW wr a) := rfl

lemma exW_mkR_node (wr : WRet n) (θ : AHid n) (a : Ix n) :
    exW (mkR wr θ) a = exWn (mkR wr θ) (gW wr a) := rfl

/-- **The node moment hypothesis**: at every World datum in the window and every node `g < J_s`,
the eighth moments over the Agent hidden matrices, restricted to the Agent event `Gs`, are at
most `F⁸` and `E⁸`. -/
def NodeMom (Gs : Set (WRet n × AHid n)) (F E : ℝ) : Prop :=
  ∀ wr : WRet n, windowW wr → ∀ g < Js n,
    ∫⁻ θ in {θ | (wr, θ) ∈ Gs}, ENNReal.ofReal (exFn (mkR wr θ) g ^ 8) ∂nuA n ≤
        ENNReal.ofReal (F ^ 8) ∧
      ∫⁻ θ in {θ | (wr, θ) ∈ Gs}, ENNReal.ofReal (exWn (mkR wr θ) g ^ 8) ∂nuA n ≤
        ENNReal.ofReal (E ^ 8)

/-- **The charge at a fixed World datum**: `ν_A{θ : (wr, θ) ∉ SB} ≤ δ_G + (F/A_f)⁸ + (E/A_ω)⁸`. -/
theorem world_charge (hn : 1 ≤ n) {Gs : Set (WRet n × AHid n)} (hG : MeasurableSet Gs)
    {δG F E Af Aw : ℝ} (hAf : 0 < Af) (hAw : 0 < Aw) (hM : NodeMom Gs F E) (wr : WRet n)
    (hδG : (nuA n).real {θ | (wr, θ) ∉ Gs} ≤ δG) :
    (nuA n).real {θ | (wr, θ) ∉ SB Gs Af Aw} ≤ δG + (F / Af) ^ 8 + (E / Aw) ^ 8 := by
  have hδ0 : 0 ≤ δG := measureReal_nonneg.trans hδG
  by_cases hw : windowW wr
  · have hGθ : MeasurableSet {θ : AHid n | (wr, θ) ∈ Gs} := measurable_prodMk_left hG
    have mC : Measurable (fun p : AHid n × Ix n => mkR wr p.1) :=
      measurable_mkR.comp (measurable_const.prodMk measurable_fst)
    have hsub : {θ | (wr, θ) ∉ SB Gs Af Aw} ⊆ ({θ | (wr, θ) ∉ Gs} ∪
        {θ | θ ∈ {θ | (wr, θ) ∈ Gs} ∧ Af ^ 8 < ∫ a, exF (mkR wr θ) a ^ 8 ∂muI n}) ∪
        {θ | θ ∈ {θ | (wr, θ) ∈ Gs} ∧ Aw ^ 8 < ∫ a, exW (mkR wr θ) a ^ 8 ∂muI n} := by
      intro θ hθ
      simp only [SB, Set.mem_ofPred_eq, not_imp, not_and, not_le] at hθ
      obtain ⟨-, h⟩ := hθ
      by_cases h1 : (wr, θ) ∈ Gs
      · by_cases h2 : intF (mkR wr θ) ≤ Af ^ 8
        · exact Or.inr ⟨h1, h1 |> h |> fun h' => h' h2⟩
        · exact Or.inl (Or.inr ⟨h1, lt_of_not_ge h2⟩)
      · exact Or.inl (Or.inl h1)
    have hF := markov_tonelli (X := fun θ a => exF (mkR wr θ) a)
      (measurable_exF_joint mC measurable_snd) (fun θ => bdd_exF hn (mkR wr θ)) hGθ hAf
      (fun a => (hM wr hw (gW wr a) (gIdx_lt _ hn _)).1)
    have hW := markov_tonelli (X := fun θ a => exW (mkR wr θ) a)
      (measurable_exW_joint mC measurable_snd) (fun θ => bdd_exW hn (mkR wr θ)) hGθ hAw
      (fun a => (hM wr hw (gW wr a) (gIdx_lt _ hn _)).2)
    have hF' := ENNReal.toReal_le_of_le_ofReal (by positivity) hF
    have hW' := ENNReal.toReal_le_of_le_ofReal (by positivity) hW
    refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
    have := measureReal_union_le (μ := nuA n) {θ | (wr, θ) ∉ Gs}
      {θ | θ ∈ {θ | (wr, θ) ∈ Gs} ∧ Af ^ 8 < ∫ a, exF (mkR wr θ) a ^ 8 ∂muI n}
    have e1 : (nuA n).real {θ | θ ∈ {θ | (wr, θ) ∈ Gs} ∧
        Af ^ 8 < ∫ a, exF (mkR wr θ) a ^ 8 ∂muI n} ≤ (F / Af) ^ 8 := hF'
    have e2 : (nuA n).real {θ | θ ∈ {θ | (wr, θ) ∈ Gs} ∧
        Aw ^ 8 < ∫ a, exW (mkR wr θ) a ^ 8 ∂muI n} ≤ (E / Aw) ^ 8 := hW'
    linarith
  · have e : {θ : AHid n | (wr, θ) ∉ SB Gs Af Aw} = ∅ := by
      ext θ
      simp only [SB, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact fun h => absurd h hw
    rw [e, measureReal_empty]
    positivity

/-- **The charge of the bias event**: `Pr(Ebiasᶜ) ≤ δ_G + (F/A_f)⁸ + (E/A_ω)⁸`. -/
theorem Ebias_charge (hn : 1 ≤ n) (D : Centres n) {Gs : Set (WRet n × AHid n)}
    (hG : MeasurableSet Gs) {δG F E Af Aw : ℝ} (hAf : 0 < Af) (hAw : 0 < Aw)
    (hM : NodeMom Gs F E) (hδG : ∀ wr : WRet n, (nuA n).real {θ | (wr, θ) ∉ Gs} ≤ δG) :
    (retDist D).real (Ebias Gs Af Aw)ᶜ ≤ δG + (F / Af) ^ 8 + (E / Aw) ^ 8 := by
  have hδ0 : 0 ≤ δG := measureReal_nonneg.trans (hδG (Classical.arbitrary _))
  exact retDist_pair_charge D (measurableSet_SB hG Af Aw) (by positivity)
    (fun wr => world_charge hn hG hAf hAw hM wr (hδG wr))

end BstLean.Part170
