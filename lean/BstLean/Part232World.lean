import BstLean.Part232Master
import BstLean.Part227Package
import BstLean.Part203Network

/-! Part 232: the parameterized World package supplies the actual LM radius moment. -/
namespace BstLean.Part232
open MeasureTheory Real Set
open BstLean.Part156
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part192 BstLean.Part203

/-- The actual independent draws have the analytic root-deviation payment. -/
theorem draw_root_charge {n : ℕ} (D : Design n) (t : ℝ) (k : ℕ)
    (x : Ret n) {ds : ℝ} (hds : 0 < ds) :
    (sampMeas k n).real
      {s | ds < |√(BstLean.Part156.hitFrac (hits D t k) (x, s)) - √(qTilde D t x)|} ≤
        2 * exp (-(k : ℝ) * ds ^ 2) :=
  BstLean.Part156.sampling_root (hits_indep D t k x)
    (fun i => (measurable_hits D t k i).comp measurable_prodMk_left)
    (fun i s => hits_01 D t k i (x, s)) (hits_mean D t k x) hds

/-- Radius cells restrict retained data; their residual distributions remain unchanged. -/
def worldCell {n : ℕ} (D : Design n) (E : Set (Ret n)) (cover : RadiusCover)
    (i : ℕ) : Set (Ret n) :=
  E ∩ {x | radiusCell cover.h i (HbarW D x)}

lemma measurableSet_worldCell {n : ℕ} (D : Design n) {E : Set (Ret n)}
    (hE : MeasurableSet E) (cover : RadiusCover) (i : ℕ) :
    MeasurableSet (worldCell D E cover i) := by
  unfold worldCell radiusCell
  by_cases hi : i = 0
  · simp only [hi, ite_true]
    exact hE.inter ((measurableSet_le measurable_const (measurable_HbarW D)).inter
      (measurableSet_le (measurable_HbarW D) measurable_const))
  · simp only [hi, ite_false]
    exact hE.inter ((measurableSet_lt measurable_const (measurable_HbarW D)).inter
      (measurableSet_le (measurable_HbarW D) measurable_const))

/-- The S10 moment restricts to any retained event inside the hidden event. -/
theorem world_retained_moment {n : ℕ} {P : Program n} {w : WorldParameters}
    (W : WorldPackage P w) {E : Set (Ret n)} (hsub : E ⊆ Hof W.hidden) :
    IntegrableOn (fun x => HbarW P.design x ^ 2) E (retDist P.design.toCentres) ∧
      ∫ x in E, HbarW P.design x ^ 2 ∂retDist P.design.toCentres ≤ w.moment := by
  refine ⟨W.moment_integrable.mono_set hsub, ?_⟩
  exact (setIntegral_mono_set W.moment_integrable
    (Filter.Eventually.of_forall fun x => sq_nonneg _) (Filter.Eventually.of_forall hsub)).trans
      W.restricted_moment

/-- The actual frame and Hellinger replacement supply FreeCPR at each cell's upper radius. -/
theorem world_cell_cpr {n : ℕ} (hn : 1 ≤ n) {P : Program n} {w : WorldParameters}
    (W : WorldPackage P w) (t : ℝ) {E : Set (Ret n)} (hsub : E ⊆ Hof W.hidden)
    (cover : RadiusCover) {i : ℕ} (hi : i < cover.K) {f : ℝ}
    (hc : 0 < w.frame) (hf : 0 < f)
    (hFA : FRAME_A_hyp P.design (f / n) (worldCell P.design E cover i)) :
    ∀ x ∈ worldCell P.design E cover i,
      FreeCPR ((resW n).prod (resA n)) (pRes P.design.toCentres t x)
        n w.frame f (cover.h (i + 1)) (QStand P.design t x) := by
  apply network_free_cpr hn P.design t hc hf (cover.nonneg (by omega))
    (fun x hx => W.frame_bound x (hsub hx.1)) hFA
  intro x hx ω hT
  exact (replw_hellinger hn P.design x hT).trans hx.2.2

/-- LM for the actual retained classifier and draw program uses the S10 restricted moment. -/
theorem world_lm {n : ℕ} (hn : 1 ≤ n) {P : Program n} {w : WorldParameters}
    (W : WorldPackage P w) (t : ℝ) (k : ℕ) {E : Set (Ret n)}
    (hE : MeasurableSet E) (hsub : E ⊆ Hof W.hidden) (cover : RadiusCover)
    {f a hA ds c₀ c₁ δs δret : ℝ}
    (hc : 0 < w.frame) (hf : 0 < f) (ha : 0 < a)
    (hhA : 0 ≤ hA) (hds : 0 ≤ ds) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hδs : 0 ≤ δs)
    (cert : ∀ i, Option (EndCertificate n w.frame f a (hA + ds) (cover.h (i + 1))))
    (hline : ∀ i < cover.K, cellPayment (cert i) ≤ c₀ + c₁ * cover.h i ^ 2)
    (hterminal : 1 ≤ c₀ + c₁ * cover.h cover.K ^ 2)
    (hFA : ∀ i, i < cover.K → (cert i).isSome →
      FRAME_A_hyp P.design (f / n) (worldCell P.design E cover i))
    (hroot : ∀ x ∈ E, |√(QStand P.design t x) - √(qTilde P.design t x)| ≤ hA)
    (hsamp : ∀ x ∈ E, (sampMeas k n).real
      {s | ds < |√(hitFrac (hits P.design t k) (x, s)) - √(qTilde P.design t x)|} ≤ δs)
    (hcomp : (retDist P.design.toCentres).real Eᶜ ≤ δret) :
    ((retDist P.design.toCentres).prod (((resW n).prod (resA n)).prod (sampMeas k n))).real
      (programFailure a (fun x => pRes P.design.toCentres t x.1 x.2)
        (hitFrac (hits P.design t k))) ≤ δret + (c₀ + c₁ * w.moment) + δs := by
  have hm := world_retained_moment W hsub
  have hq : Measurable (qTilde P.design t) :=
    (measurable_hitFn P.design t).stronglyMeasurable.integral_prod_right'.measurable
  apply lm_end_master (r := HbarW P.design) (Q := QStand P.design t)
    (qt := qTilde P.design t) (retDist P.design.toCentres) ((resW n).prod (resA n))
    (sampMeas k n) hE cover (fun x => sqrt_nonneg _) hq
    (measurable_pRes P.design.toCentres t) (fun x => pRes_nonneg _ _ _ _)
    (fun x => pRes_le_one hn _ _ _ _) (measurable_hitFrac P.design t k)
    (fun x => by
      unfold hitFrac
      apply div_nonneg _ (Nat.cast_nonneg k)
      apply Finset.sum_nonneg
      intro i _
      rcases hits_01 P.design t k i x with hi | hi <;> simp [hi])
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn) : (0 : ℝ) < n)
    hc hf ha hhA hds hc₀ hc₁ hδs
    cert hm.1 hm.2 hline hterminal (fun x _ => QStand_mem_01 _ _ x) hroot _ hsamp hcomp
  intro x hx i hi hcell hsome
  exact world_cell_cpr hn W t hsub cover hi hc hf (hFA i hi hsome) x ⟨hx, hcell⟩

end BstLean.Part232
