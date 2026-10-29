import BstLean.Part170Mom

/-!
# Part 170 (file `Fin`): the bias event with free statistics events; the end theorem

No proof is left open; no `native_decide` or `axiom` is used.

The event of file `Ev` asks `(wr, θ) ∈ Gs` and so charges `Gs` again. Here the operator part of
`Gs` is NOT charged again: the good set already contains Lean's operator event for `A₁`
(`opB_goodD`). The bias event is `Ebm ∩ EGb`:

* `SB2 Gs A_f A_ω`: if `wr` is in the window and `(wr, θ) ∈ Gs`, then `intF ≤ A_f⁸` and
  `intW ≤ A_ω⁸`; `Ebm = {c | (c.1, (A₁, A₂)) ∈ SB2}`; charge `(F/A_f)⁸ + (E/A_ω)⁸` (`Ebm_charge`).
* `EGb Gb = {c | window → (c.1, A₁) ∈ Gb}`: the free first-layer statistics event; charge `δ_G`.
* `F_fl ≤ 0.0101` for every `n ≥ 80 000` (`Ffl_le`).
* **`classifier_paper_fl80k`**: the classifier theorem (every `n ≥ 80 000`, with `E_A = univ`).
  Remaining hypotheses: a measurable family `Gb` of first-layer events with charge `δ_G`; the bias
  moments `BiasMomF (O1n n) Gb B_f` of the location pass; the node moments `E` of the energy pass
  on `GsOf (O1n n) Gb`; `A_ω + 8.06A_f ≤ 0.72`; and
  `δ_G + ((F_fl + B_f)/A_f)⁸ + (E/A_ω)⁸ ≤ roomE`.
-/

namespace BstLean.Part170

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part153 (nuA)
open BstLean.Part166 (goodD)

variable {n : ℕ}

/-- The pairs of the Markov part of the bias event. -/
def SB2 (Gs : Set (WRet n × AHid n)) (Af Aw : ℝ) : Set (WRet n × AHid n) :=
  {p | windowW p.1 → p ∈ Gs → intF (mkR p.1 p.2) ≤ Af ^ 8 ∧ intW (mkR p.1 p.2) ≤ Aw ^ 8}

lemma measurableSet_SB2 {Gs : Set (WRet n × AHid n)} (hG : MeasurableSet Gs) (Af Aw : ℝ) :
    MeasurableSet (SB2 Gs Af Aw) := by
  have hw : MeasurableSet {p : WRet n × AHid n | windowW p.1} :=
    measurable_fst measurableSet_windowW
  have h1 : MeasurableSet {p : WRet n × AHid n | intF (mkR p.1 p.2) ≤ Af ^ 8} :=
    measurableSet_le (measurable_intF_comp measurable_mkR) measurable_const
  have h2 : MeasurableSet {p : WRet n × AHid n | intW (mkR p.1 p.2) ≤ Aw ^ 8} :=
    measurableSet_le (measurable_intW_comp measurable_mkR) measurable_const
  have e : SB2 Gs Af Aw = {p : WRet n × AHid n | windowW p.1}ᶜ ∪ (Gsᶜ ∪ ({p : WRet n × AHid n |
      intF (mkR p.1 p.2) ≤ Af ^ 8} ∩ {p : WRet n × AHid n | intW (mkR p.1 p.2) ≤ Aw ^ 8})) := by
    ext p
    simp only [SB2, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
    tauto
  rw [e]
  exact hw.compl.union (hG.compl.union (h1.inter h2))

/-- The Markov part of the bias event. -/
def Ebm (Gs : Set (WRet n × AHid n)) (Af Aw : ℝ) : Set (Ret n) :=
  {c | (c.1, c.2.1.1) ∈ SB2 Gs Af Aw}

/-- The pairs of the statistics event. -/
def SG (Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)) : Set (WRet n × AHid n) :=
  {p | windowW p.1 → (p.1, p.2.1) ∈ Gb}

lemma measurableSet_SG {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : MeasurableSet Gb) : MeasurableSet (SG Gb) := by
  have hw : MeasurableSet {p : WRet n × AHid n | windowW p.1} :=
    measurable_fst measurableSet_windowW
  have h1 : MeasurableSet {p : WRet n × AHid n | (p.1, p.2.1) ∈ Gb} :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) hGb
  have e : SG Gb = {p : WRet n × AHid n | windowW p.1}ᶜ ∪ {p : WRet n × AHid n | (p.1, p.2.1) ∈ Gb} := by
    ext p; simp only [SG, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]; tauto
  rw [e]; exact hw.compl.union h1

/-- The statistics event: in the window, `(wr, A₁) ∈ Gb`. -/
def EGb (Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)) : Set (Ret n) :=
  {c | (c.1, c.2.1.1) ∈ SG Gb}

/-- **The bias event.** -/
def EbiasF (O : ℝ) (Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)) (Af Aw : ℝ) : Set (Ret n) :=
  Ebm (GsOf O Gb) Af Aw ∩ EGb Gb

lemma measurableSet_EbiasF (O : ℝ) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : MeasurableSet Gb) (Af Aw : ℝ) : MeasurableSet (EbiasF O Gb Af Aw) := by
  have hk : Measurable (fun c : Ret n => ((c.1, c.2.1.1) : WRet n × AHid n)) :=
    measurable_fst.prodMk (measurable_fst.comp (measurable_fst.comp measurable_snd))
  exact (hk (measurableSet_SB2 (measurableSet_GsOf O hGb) Af Aw)).inter (hk (measurableSet_SG hGb))

/-- **Markov at a fixed World datum** (no charge for `Gs`). -/
theorem world_charge2 (hn : 1 ≤ n) {Gs : Set (WRet n × AHid n)} (hG : MeasurableSet Gs)
    {F E Af Aw : ℝ} (hAf : 0 < Af) (hAw : 0 < Aw) (hM : NodeMom Gs F E) (wr : WRet n) :
    (nuA n).real {θ | (wr, θ) ∉ SB2 Gs Af Aw} ≤ (F / Af) ^ 8 + (E / Aw) ^ 8 := by
  by_cases hw : windowW wr
  · have hGθ : MeasurableSet {θ : AHid n | (wr, θ) ∈ Gs} := measurable_prodMk_left hG
    have mC : Measurable (fun p : AHid n × Ix n => mkR wr p.1) :=
      measurable_mkR.comp (measurable_const.prodMk measurable_fst)
    have hsub : {θ | (wr, θ) ∉ SB2 Gs Af Aw} ⊆
        {θ | θ ∈ {θ | (wr, θ) ∈ Gs} ∧ Af ^ 8 < ∫ a, exF (mkR wr θ) a ^ 8 ∂muI n} ∪
        {θ | θ ∈ {θ | (wr, θ) ∈ Gs} ∧ Aw ^ 8 < ∫ a, exW (mkR wr θ) a ^ 8 ∂muI n} := by
      intro θ hθ
      simp only [SB2, Set.mem_ofPred_eq, not_imp, not_and, not_le] at hθ
      obtain ⟨-, h1, h⟩ := hθ
      by_cases h2 : intF (mkR wr θ) ≤ Af ^ 8
      · exact Or.inr ⟨h1, h h2⟩
      · exact Or.inl ⟨h1, lt_of_not_ge h2⟩
    have hF := markov_tonelli (X := fun θ a => exF (mkR wr θ) a)
      (measurable_exF_joint mC measurable_snd) (fun θ => bdd_exF hn (mkR wr θ)) hGθ hAf
      (fun a => (hM wr hw (gW wr a) (gIdx_lt _ hn _)).1)
    have hW := markov_tonelli (X := fun θ a => exW (mkR wr θ) a)
      (measurable_exW_joint mC measurable_snd) (fun θ => bdd_exW hn (mkR wr θ)) hGθ hAw
      (fun a => (hM wr hw (gW wr a) (gIdx_lt _ hn _)).2)
    have hF' := ENNReal.toReal_le_of_le_ofReal (by positivity) hF
    have hW' := ENNReal.toReal_le_of_le_ofReal (by positivity) hW
    refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
    exact add_le_add hF' hW'
  · have e : {θ : AHid n | (wr, θ) ∉ SB2 Gs Af Aw} = ∅ := by
      ext θ
      simp only [SB2, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact fun h => absurd h hw
    rw [e, measureReal_empty]
    positivity

/-- **The charge of the bias event**: `Pr(EbiasFᶜ) ≤ δ_G + (F/A_f)⁸ + (E/A_ω)⁸`. -/
theorem EbiasF_charge (hn : 1 ≤ n) (D : Centres n) {O : ℝ}
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {δG F E Af Aw : ℝ}
    (hδ0 : 0 ≤ δG) (hAf : 0 < Af) (hAw : 0 < Aw) (hM : NodeMom (GsOf O Gb) F E)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ δG) :
    (retDist D).real (EbiasF O Gb Af Aw)ᶜ ≤ δG + (F / Af) ^ 8 + (E / Aw) ^ 8 := by
  have h1 := retDist_pair_charge D (measurableSet_SB2 (measurableSet_GsOf O hGb) Af Aw)
    (by positivity) (fun wr => world_charge2 hn (measurableSet_GsOf O hGb) hAf hAw hM wr)
  have h2 := retDist_pair_charge D (measurableSet_SG hGb) hδ0 (fun wr => by
    by_cases hw : windowW wr
    · refine (measureReal_mono ?_).trans (hδG wr hw)
      intro θ hθ; simp only [SG, Set.mem_ofPred_eq, not_imp] at hθ ⊢; exact hθ.2
    · have e : {θ : AHid n | (wr, θ) ∉ SG Gb} = ∅ := by
        ext θ; simp only [SG, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
        exact fun h => absurd h hw
      rw [e, measureReal_empty]; exact hδ0)
  have hsub : (EbiasF O Gb Af Aw)ᶜ ⊆ {c : Ret n | (c.1, c.2.1.1) ∉ SB2 (GsOf O Gb) Af Aw} ∪
      {c : Ret n | (c.1, c.2.1.1) ∉ SG Gb} := by
    intro c hc
    simp only [EbiasF, Ebm, EGb, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hc
    exact hc
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ (F / Af) ^ 8 + (E / Aw) ^ 8 + δG := add_le_add h1 h2
    _ = _ := by ring

/-- `MomZ` on the good set with the bias event. -/
theorem momZ_of_EbiasF (hn : 80000 ≤ n) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    {Af Aw : ℝ} {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) (EA ∩ EbiasF (O1n n) Gb Af Aw)) : MomZ c Af Aw := by
  have hn1 : 1 ≤ n := by omega
  have hw := windowW_of_goodD (by omega) hc
  have hE : c ∈ EbiasF (O1n n) Gb Af Aw := Ebias_of_goodD hc
  have hop := (opB_goodD (by omega) hc).1
  have hGs : (c.1, c.2.1.1) ∈ GsOf (O1n n) Gb := ⟨hop, hE.2 hw⟩
  obtain ⟨hF, hW⟩ := hE.1 hw hGs
  exact ⟨(int_pow8_le_univ (measurable_exF c) (bdd_exF hn1 c) _).trans hF,
    (int_pow8_le_univ (measurable_exW c) (bdd_exW hn1 c) _).trans hW⟩

/-- The energy node moments on `Gs` (the remaining hypothesis of the energy half). -/
def NodeMomW (Gs : Set (WRet n × AHid n)) (E : ℝ) : Prop :=
  ∀ wr : WRet n, windowW wr → ∀ g < Js n,
    ∫⁻ θ in {θ | (wr, θ) ∈ Gs}, ENNReal.ofReal (exWn (mkR wr θ) g ^ 8) ∂nuA n ≤
      ENNReal.ofReal (E ^ 8)

lemma Ffl_le (hn : 80000 ≤ n) : Ffl n (O1n n) ≤ 101 / 10000 := by
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hs283 : 282 ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hn0.le]; nlinarith
  -- `√n·√X = √(nX)`, `nX = 4(1 + 2/√n)²/(n − 2)`
  have hX : (n : ℝ) * (tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) =
      4 * (1 + 2 / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
    unfold tA O1n mA
    push_cast
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    set r := √(n : ℝ) with hr
    have hnr : (n : ℝ) = r ^ 2 := hsq.symm
    have hr2 : r ^ 2 - 2 ≠ 0 := by nlinarith
    rw [hnr]
    field_simp
    ring
  have hX2 : 4 * (1 + 2 / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) ≤ (713 / 100000) ^ 2 := by
    have h1 : 2 / √(n : ℝ) ≤ 2 / 282 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs283
    have h2 : (1 + 2 / √(n : ℝ)) ^ 2 ≤ (1 + 2 / 282) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hpi : π ≤ 3.1416 := Real.pi_lt_d4.le
  have hroot : √(n : ℝ) * √(tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) ≤ 713 / 100000 := by
    rw [← Real.sqrt_mul hn0.le, hX]
    rw [Real.sqrt_le_left (by norm_num)]; exact hX2
  unfold Ffl
  have e : π / 2 * (18 / 10) * √(n : ℝ) * √(tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) / 2 =
      π / 2 * (18 / 10) / 2 * (√(n : ℝ) * √(tA n * (O1n n ^ 2 / ((n : ℝ) - 2)))) := by ring
  rw [e]
  have h0 : 0 ≤ √(n : ℝ) * √(tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) := by positivity
  nlinarith [Real.pi_pos]

/-- **The classifier theorem with the location fluctuation proved** (every `n ≥ 80 000`,
`E_A = univ`). Remaining: a measurable family `Gb` of first-layer events (charge `δ_G` in the
window); the bias moments of the location pass `BiasMomF (O1n n) Gb B_f`; the energy node moments
`NodeMomW (GsOf (O1n n) Gb) E`; the linear condition; and
`δ_G + ((F_fl + B_f)/A_f)⁸ + (E/A_ω)⁸ ≤ roomE`. -/
theorem classifier_paper_fl80k (hn : 80000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {δG : ℝ}
    (hδ0 : 0 ≤ δG)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ δG)
    {Bf E Af Aw : ℝ} (hBf : 0 < Bf) (hAf : 0 < Af) (hAw : 0 < Aw)
    (hlin : Aw + 806 / 100 * Af ≤ 72 / 100)
    (hBias : BiasMomF (O1n n) Gb Bf) (hW : NodeMomW (GsOf (O1n n) Gb) E)
    (hroom : δG + ((Ffl n (O1n n) + Bf) / Af) ^ 8 + (E / Aw) ^ 8 ≤ BstLean.Part167.roomE) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  have hO : 0 < O1n n := O1n_pos hn1
  have hM : NodeMom (GsOf (O1n n) Gb) (Ffl n (O1n n) + Bf) E := fun wr hw g hg =>
    ⟨nodeMomF_of_bias hn hO hGb hBf hBias wr hw g hg, hW wr hw g hg⟩
  have hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩
      (Set.univ : Set (Ret n))ᶜ) ≤ 0 := by
    rw [Set.compl_univ, Set.inter_empty, measureReal_empty]
  exact classifier_paper_A80k hn t MeasurableSet.univ (measurableSet_EbiasF (O1n n) hGb Af Aw) hA
    (EbiasF_charge hn1 (paperCentres n) hGb hδ0 hAf hAw hM hδG) (by linarith) hAf hAw hlin
    (fun c hc => momZ_of_EbiasF hn hc)

end BstLean.Part170
