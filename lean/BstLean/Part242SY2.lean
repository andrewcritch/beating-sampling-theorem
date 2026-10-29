import BstLean.Part242ConditionalSD

/-! SY2 uses one complete transverse distribution and its actual good restrictions. -/
namespace BstLean.Part242
open MeasureTheory Real Set
open scoped ENNReal

variable {A V : Type*} [MeasurableSpace A] [MeasurableSpace V]

lemma goodMeanSq_eq_goodMean (ν : Measure V) [IsProbabilityMeasure ν]
    {G : Set (A × V)} (hG : MeasurableSet G) {z : A × V → ℝ} (a : A) :
    goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v)) =
      BstLean.Part161.goodMean ν G z a ^ 2 := by
  have ms : MeasurableSet {v | (a, v) ∈ G} := hG.preimage measurable_prodMk_left
  have mass : ν.real {v | (a, v) ∈ G} = 1 - BstLean.Part161.removed ν G a := by
    have hcomp := measureReal_compl (μ := ν) ms
    change ν.real {v | (a, v) ∉ G} = ν.real univ - ν.real {v | (a, v) ∈ G} at hcomp
    rw [probReal_univ] at hcomp
    unfold BstLean.Part161.removed
    linarith
  unfold goodMeanSq BstLean.Part162.nrm
  rw [integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal measureReal_nonneg, ← integral_indicator ms, mass, smul_eq_mul]
  unfold BstLean.Part161.goodMean
  congr 1
  have ie : (fun v => ({v | (a, v) ∈ G}).indicator (fun v => z (a, v)) v) =
      fun v => G.indicator z (a, v) := by
    funext v
    by_cases h : (a, v) ∈ G <;> simp [h]
  rw [ie]
  ring

theorem SY2_conditional (ρ : Measure A) (ν : Measure V) [SFinite ρ]
    [IsProbabilityMeasure ν] (hmass : ρ univ ≤ 1)
    {K : Set A} (hK : MeasurableSet K) {G : Set (A × V)} (hG : MeasurableSet G)
    {z : A × V → ℝ} {M d Y0 H μ0 g8 η τ8 Vbound : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hd : 0 < d) (hY0 : d < Y0)
    (hgood : ∀ a, 1 - η ≤ ν.real {v | (a, v) ∈ G})
    (hM : ∀ a v, |z (a, v)| ≤ M)
    (hz : LBound (ρ.prod ν) 8 z (1 + H))
    (hc : LBound (ρ.prod ν) 8 (fun q => z q - latitudeMean ν z q.1) τ8)
    (hvar : LBound ρ 4 (fun a => conditionalVariance ν (fun v => z (a, v))) Vbound)
    (hbase : LBound ρ 4 (fun a => max 0 (Y0 - latitudeMean ν (fun q => z q ^ 2) a))
      (2 * H + g8 * (2 * μ0 + g8)))
    (hfloor : ∀ a ∈ K, d ≤ goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v))) :
    LBound (ρ.restrict K) 4
      (fun a => 1 / goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v)))
      (gMix d Y0 H μ0 g8 η τ8 Vbound) := by
  have hsd := conditional_squareSD ρ ν hM hz hc
  have mz : Measurable
      (fun a => goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v))) := by
    have he : (fun a => goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v))) =
        fun a => BstLean.Part161.goodMean ν G z a ^ 2 := by
      funext a
      exact goodMeanSq_eq_goodMean ν hG a
    rw [he]
    exact (BstLean.Part161.measurable_goodMean ν hG hz.measurable).pow_const 2
  apply SY2 hK hmass mz hd hY0 hη0 hη1 hfloor hbase hsd hvar
  intro a
  have h := good_scale_loss ν (hG.preimage measurable_prodMk_left) hη0 hη1 (hgood a)
    (hz.measurable.comp measurable_prodMk_left) (hM a)
  have hv0 : 0 ≤ conditionalVariance ν (fun v => z (a, v)) :=
    integral_nonneg fun v => sq_nonneg _
  simpa only [squareSD, latitudeMean, Function.comp_def, Set.preimage,
    abs_of_nonneg (sqrt_nonneg _), abs_of_nonneg hv0] using h

/-- Only kept indices require a lower bound on the good transverse mass. -/
theorem SY2_kept (ρ : Measure A) (ν : Measure V) [SFinite ρ]
    [IsProbabilityMeasure ν] (hmass : ρ univ ≤ 1)
    {K : Set A} (hK : MeasurableSet K) {G : Set (A × V)} (hG : MeasurableSet G)
    {z : A × V → ℝ} {M d Y0 H μ0 g8 η τ8 Vbound : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hd : 0 < d) (hY0 : d < Y0)
    (hgood : ∀ a ∈ K, 1 - η ≤ ν.real {v | (a, v) ∈ G})
    (hM : ∀ a v, |z (a, v)| ≤ M)
    (hz : LBound (ρ.prod ν) 8 z (1 + H))
    (hc : LBound (ρ.prod ν) 8 (fun q => z q - latitudeMean ν z q.1) τ8)
    (hvar : LBound ρ 4 (fun a => conditionalVariance ν (fun v => z (a, v))) Vbound)
    (hbase : LBound ρ 4 (fun a => max 0 (Y0 - latitudeMean ν (fun q => z q ^ 2) a))
      (2 * H + g8 * (2 * μ0 + g8)))
    (hfloor : ∀ a ∈ K, d ≤ goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v))) :
    LBound (ρ.restrict K) 4
      (fun a => 1 / goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v)))
      (gMix d Y0 H μ0 g8 η τ8 Vbound) := by
  let Gplus : Set (A × V) := G ∪ (Kᶜ ×ˢ univ)
  have mGplus : MeasurableSet Gplus := hG.union (hK.compl.prod MeasurableSet.univ)
  have eqKept : ∀ a ∈ K, {v | (a, v) ∈ Gplus} = {v | (a, v) ∈ G} := by
    intro a ha
    ext v
    simp [Gplus, ha]
  have massPlus : ∀ a, 1 - η ≤ ν.real {v | (a, v) ∈ Gplus} := by
    intro a
    by_cases ha : a ∈ K
    · rw [eqKept a ha]
      exact hgood a ha
    · have hfull : {v | (a, v) ∈ Gplus} = univ := by ext v; simp [Gplus, ha]
      rw [hfull, probReal_univ]
      linarith
  have floorPlus : ∀ a ∈ K, d ≤ goodMeanSq ν {v | (a, v) ∈ Gplus} (fun v => z (a, v)) :=
    fun a ha => by rw [eqKept a ha]; exact hfloor a ha
  have h := SY2_conditional ρ ν hmass hK mGplus hη0 hη1 hd hY0 massPlus hM hz hc
    hvar hbase floorPlus
  have mOrig : Measurable (fun a => 1 / goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v))) := by
    have he : (fun a => 1 / goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v))) =
        fun a => 1 / BstLean.Part161.goodMean ν G z a ^ 2 := by
      funext a
      rw [goodMeanSq_eq_goodMean ν hG a]
    rw [he]
    exact measurable_const.div ((BstLean.Part161.measurable_goodMean ν hG hz.measurable).pow_const 2)
  apply h.mono mOrig
  apply (ae_restrict_iff' hK).mpr
  exact Filter.Eventually.of_forall fun a ha => by rw [eqKept a ha]

end BstLean.Part242
