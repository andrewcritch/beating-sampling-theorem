import BstLean.Part232World

/-! Part 232: the retained LM ledger transfers to the original networks and program. -/
namespace BstLean.Part232
open MeasureTheory Real Set
open BstLean.Part156
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part192

/-- The hidden and extra retained complements have separate single payments. -/
theorem world_extra_complement {n : ℕ} {P : Program n} {w : WorldParameters}
    (W : WorldPackage P w) {E : Set (Ret n)} {δextra : ℝ}
    (hExtra : (retDist P.design.toCentres).real (Hof W.hidden ∩ Eᶜ) ≤ δextra) :
    (retDist P.design.toCentres).real (Hof W.hidden ∩ E)ᶜ ≤ w.hiddenCharge + δextra := by
  have hsub : (Hof W.hidden ∩ E)ᶜ ⊆ (Hof W.hidden)ᶜ ∪ (Hof W.hidden ∩ Eᶜ) := by
    intro x hx
    by_cases hh : x ∈ Hof W.hidden
    · exact Or.inr ⟨hh, fun he => hx ⟨hh, he⟩⟩
    · exact Or.inl hh
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add (world_retained_charge W) hExtra))

/-- The full retained product failure is exactly the failure of the original network program. -/
theorem retained_failure_eq {n : ℕ} (D : Design n) (t a : ℝ) (k : ℕ) :
    ((mlpTriple 2 n).prod (sampMeas k n)).real (failNet D t a k) =
      ((retDist D.toCentres).prod (((resW n).prod (resA n)).prod (sampMeas k n))).real
        (programFailure a (fun x => pRes D.toCentres t x.1 x.2) (hitFrac (hits D t k))) := by
  have mr := measurable_retVal D.toCentres
  have mf := measurableSet_programFailure (measurable_pRes D.toCentres t)
    (measurable_hitFrac D t k) (a := a)
  have he : ((noiseC n).prod (((resW n).prod (resA n)).prod (sampMeas k n))).map
      (Prod.map (retVal D.toCentres) id) =
      (retDist D.toCentres).prod (((resW n).prod (resA n)).prod (sampMeas k n)) := by
    rw [← Measure.map_prod_map _ _ mr measurable_id, noise_retVal, Measure.map_id]
  rw [failNet_eq, ← he, map_measureReal_apply (mr.prodMap measurable_id) mf]
  rfl

/-- A checked retained LM ledger gives the unchanged classifier success criterion. -/
theorem classifier_of_retained_lm {n : ℕ} (D : Design n) (t a : ℝ) (k : ℕ) {B : ℝ}
    (hB : ((retDist D.toCentres).prod
      (((resW n).prod (resA n)).prod (sampMeas k n))).real
        (programFailure a (fun x => pRes D.toCentres t x.1 x.2) (hitFrac (hits D t k))) ≤ B) :
    1 - B ≤ ((mlpTriple 2 n).prod (sampMeas k n)).real
      {x | successNet x.1 t (progOut D t a k x.1 x.2)} := by
  have hfail := hB
  rw [← retained_failure_eq] at hfail
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have he : {x : Net3 n × (Fin k → DrawSp n) |
      successNet x.1 t (progOut D t a k x.1 x.2)} = (failNet D t a k)ᶜ := by
    ext x
    simp [failNet]
  rw [he, measureReal_compl (measurableSet_failNet D t a k), probReal_univ]
  linarith

/-- The complete LM ledger retains the original classifier program and pays draws once. -/
theorem classifier_lm {n : ℕ} (hn : 1 ≤ n) {P : Program n} {w : WorldParameters}
    (W : WorldPackage P w) (t : ℝ) (k : ℕ) {E : Set (Ret n)}
    (hE : MeasurableSet E) (cover : RadiusCover)
    {f a hA ds c₀ c₁ δextra : ℝ}
    (hc : 0 < w.frame) (hf : 0 < f) (ha : 0 < a)
    (hhA : 0 ≤ hA) (hds : 0 < ds) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (cert : ∀ i, Option
      (EndCertificate n w.frame f a (hA + ds) (cover.h (i + 1))))
    (hline : ∀ i < cover.K, cellPayment (cert i) ≤ c₀ + c₁ * cover.h i ^ 2)
    (hterminal : 1 ≤ c₀ + c₁ * cover.h cover.K ^ 2)
    (hFA : ∀ i, i < cover.K → (cert i).isSome →
      FRAME_A_hyp P.design (f / n)
        (worldCell P.design (Hof W.hidden ∩ E) cover i))
    (hroot : ∀ x ∈ Hof W.hidden ∩ E,
      |√(QStand P.design t x) - √(qTilde P.design t x)| ≤ hA)
    (hExtra : (retDist P.design.toCentres).real (Hof W.hidden ∩ Eᶜ) ≤ δextra) :
    1 - (w.hiddenCharge + δextra + (c₀ + c₁ * w.moment) +
      2 * exp (-(k : ℝ) * ds ^ 2)) ≤
      ((mlpTriple 2 n).prod (sampMeas k n)).real
        {x | successNet x.1 t (progOut P.design t a k x.1 x.2)} := by
  apply classifier_of_retained_lm
  exact world_lm hn W t k ((measurableSet_Hof W.hidden_measurable).inter hE)
    (fun x hx => hx.1) cover hc hf ha hhA hds.le hc₀ hc₁ (by positivity)
    cert hline hterminal hFA hroot (fun x _ => draw_root_charge P.design t k x hds)
    (world_extra_complement W hExtra)

end BstLean.Part232
