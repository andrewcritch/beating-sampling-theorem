import BstLean.Part248Norm
import BstLean.Part248Mixture

/-! Orders four, eight and twelve give three selectable reciprocal bounds. -/
namespace BstLean.Part248
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part242

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

structure DeficitOrders (μ : Measure X) (Y : X → ℝ) (Y0 X4 X8 X12 : ℝ) : Prop where
  order4 : LBound μ 4 (fun x => max 0 (Y0 - Y x)) X4
  order8 : LBound μ 8 (fun x => max 0 (Y0 - Y x)) X8
  order12 : LBound μ 12 (fun x => max 0 (Y0 - Y x)) X12

noncomputable def threeConstants (X4 X8 X12 : ℝ) (j : ℕ) : ℝ :=
  if j = 1 then X4 else if j = 2 then X8 else X12

lemma deficit_orders {Y : X → ℝ} {Y0 X4 X8 X12 : ℝ}
    (h : DeficitOrders μ Y Y0 X4 X8 X12) {j : ℕ} (hj : 1 ≤ j) (hj3 : j ≤ 3) :
    LBound μ ((4 * j : ℕ) : ℝ≥0∞) (fun x => max 0 (Y0 - Y x))
      (threeConstants X4 X8 X12 j) := by
  have hc : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hc with rfl | rfl | rfl
  · simpa [threeConstants] using h.order4
  · simpa [threeConstants] using h.order8
  · simpa [threeConstants] using h.order12

noncomputable def bound1 (d Y0 X4 : ℝ) : ℝ := 1 / Y0 + X4 / (d * Y0)
noncomputable def bound2 (d Y0 X4 X8 : ℝ) : ℝ :=
  1 / Y0 + X4 / Y0 ^ 2 + X8 ^ 2 / (d * Y0 ^ 2)
noncomputable def bound3 (d Y0 X4 X8 X12 : ℝ) : ℝ :=
  1 / Y0 + X4 / Y0 ^ 2 + X8 ^ 2 / Y0 ^ 3 + X12 ^ 3 / (d * Y0 ^ 3)
noncomputable def bestBound (d Y0 X4 X8 X12 : ℝ) : ℝ :=
  min (bound1 d Y0 X4) (min (bound2 d Y0 X4 X8) (bound3 d Y0 X4 X8 X12))

lemma norm_min {p : ℝ≥0∞} {f : X → ℝ} {A B : ℝ}
    (ha : LBound μ p f A) (hb : LBound μ p f B) : LBound μ p f (min A B) := by
  by_cases h : A ≤ B
  · simpa only [min_eq_left h] using ha
  · simpa only [min_eq_right (le_of_not_ge h)] using hb

/-- R uses the smallest of the three completed expansions. -/
theorem R_best {K : Set X} (hK : MeasurableSet K) (hmass : μ univ ≤ 1)
    {Y : X → ℝ} (mY : Measurable Y) {d Y0 X4 X8 X12 : ℝ}
    (hd : 0 < d) (hY0 : 0 < Y0) (hfloor : ∀ x ∈ K, d ≤ Y x)
    (h : DeficitOrders μ Y Y0 X4 X8 X12) :
    LBound (μ.restrict K) 4 (fun x => 1 / Y x) (bestBound d Y0 X4 X8 X12) := by
  have hR (k : ℕ) (hk : k ≤ 3) := R_norm (q := 4) (k := k) (by omega)
    hK hmass mY hd hY0 hfloor (B := threeConstants X4 X8 X12)
    (fun j hj hjk => deficit_orders h hj (hjk.trans hk))
  have h1 : LBound (μ.restrict K) 4 (fun x => 1 / Y x) (bound1 d Y0 X4) := by
    simpa [reciprocalEstimate, threeConstants, Finset.sum_range_succ, bound1] using hR 1 (by omega)
  have h2 : LBound (μ.restrict K) 4 (fun x => 1 / Y x) (bound2 d Y0 X4 X8) := by
    simpa [reciprocalEstimate, threeConstants, Finset.sum_range_succ, bound2] using hR 2 (by omega)
  have h3 : LBound (μ.restrict K) 4 (fun x => 1 / Y x) (bound3 d Y0 X4 X8 X12) := by
    simpa [reciprocalEstimate, threeConstants, Finset.sum_range_succ, bound3] using hR 3 (by omega)
  exact norm_min h1 (norm_min h2 h3)

/-- The bias denominator uses `(1-eta)*dl`; the mixture denominator uses `dl`.
Both norms use the same original retained measure. -/
theorem distinct_floors {K : Set X} (hK : MeasurableSet K) (hmass : μ univ ≤ 1)
    {Y Z : X → ℝ} (mY : Measurable Y) (mZ : Measurable Z)
    {dl η Y0 X4 X8 X12 Z4 Z8 Z12 : ℝ} (hdl : 0 < dl) (hη : η < 1)
    (hY0 : 0 < Y0) (hYfloor : ∀ x ∈ K, (1 - η) * dl ≤ Y x)
    (hZfloor : ∀ x ∈ K, dl ≤ Z x)
    (hY : DeficitOrders μ Y Y0 X4 X8 X12) (hZ : DeficitOrders μ Z Y0 Z4 Z8 Z12) :
    LBound (μ.restrict K) 4 (fun x => 1 / Y x)
      (bestBound ((1 - η) * dl) Y0 X4 X8 X12) ∧
    LBound (μ.restrict K) 4 (fun x => 1 / Z x)
      (bestBound dl Y0 Z4 Z8 Z12) :=
  ⟨R_best hK hmass mY (by positivity) hY0 hYfloor hY,
    R_best hK hmass mZ hdl hY0 hZfloor hZ⟩

/-- Deficit inputs can already use the original kept measure. -/
theorem R_best_kept {K : Set X} (hK : MeasurableSet K) (hmass : μ univ ≤ 1)
    {Y : X → ℝ} (mY : Measurable Y) {d Y0 X4 X8 X12 : ℝ}
    (hd : 0 < d) (hY0 : 0 < Y0) (hfloor : ∀ x ∈ K, d ≤ Y x)
    (h : DeficitOrders (μ.restrict K) Y Y0 X4 X8 X12) :
    LBound (μ.restrict K) 4 (fun x => 1 / Y x) (bestBound d Y0 X4 X8 X12) := by
  have hh := R_best (μ := μ.restrict K) hK
    ((Measure.restrict_le_self univ).trans hmass) mY hd hY0 hfloor h
  simpa only [Measure.restrict_restrict hK, inter_self] using hh

noncomputable def mixtureConstant (Xq H τ η V : ℝ) : ℝ :=
  Xq + sqrt (η / (1 - η)) * (2 * (1 + H) * τ) + V / (1 - η)

/-- Conditional mixture supplies use orders 8,16,24 for centering and order12 for variance. -/
theorem mixture_orders {A V : Type*} [MeasurableSpace A] [MeasurableSpace V]
    (ρ : Measure A) (ν : Measure V) [SFinite ρ] [IsProbabilityMeasure ν]
    (hmass : ρ univ ≤ 1) {K : Set A} (hK : MeasurableSet K)
    {G : Set (A × V)} (hG : MeasurableSet G) {z : A × V → ℝ}
    {M Y0 X4 X8 X12 η H τ8 τ16 τ24 Vbound : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hgood : ∀ a ∈ K, 1 - η ≤ ν.real {v | (a, v) ∈ G})
    (hM : ∀ a v, |z (a, v)| ≤ M)
    (hz : LBound (ρ.prod ν) 24 z (1 + H))
    (hc8 : LBound (ρ.prod ν) 8 (fun q => z q - latitudeMean ν z q.1) τ8)
    (hc16 : LBound (ρ.prod ν) 16 (fun q => z q - latitudeMean ν z q.1) τ16)
    (hc24 : LBound (ρ.prod ν) 24 (fun q => z q - latitudeMean ν z q.1) τ24)
    (hvar : LBound ρ 12 (fun a => conditionalVariance ν (fun v => z (a, v))) Vbound)
    (hbase : DeficitOrders ρ (latitudeMean ν (fun q => z q ^ 2)) Y0 X4 X8 X12) :
    DeficitOrders (ρ.restrict K)
      (fun a => goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v))) Y0
      (mixtureConstant X4 H τ8 η Vbound) (mixtureConstant X8 H τ16 η Vbound)
      (mixtureConstant X12 H τ24 η Vbound) := by
  have hm : (ρ.prod ν) univ ≤ 1 := by
    rw [← univ_prod_univ, Measure.prod_prod, measure_univ (μ := ν), mul_one]
    exact hmass
  have hz8 := hz.lower (by norm_num) (by norm_num) (by norm_num : (8 : ℝ≥0∞) ≤ 24) hm
  have hz16 := hz.lower (by norm_num) (by norm_num) (by norm_num : (16 : ℝ≥0∞) ≤ 24) hm
  have hv4 := hvar.lower (by norm_num) (by norm_num) (by norm_num : (4 : ℝ≥0∞) ≤ 12) hmass
  have hv8 := hvar.lower (by norm_num) (by norm_num) (by norm_num : (8 : ℝ≥0∞) ≤ 12) hmass
  exact ⟨mixture_conditional ρ ν (p := 2) (by omega) (by decide) hK hG hη0 hη1
      hgood hM hz8 hc8 hv4 hbase.order4,
    mixture_conditional ρ ν (p := 4) (by omega) (by decide) hK hG hη0 hη1
      hgood hM hz16 hc16 hv8 hbase.order8,
    mixture_conditional ρ ν (p := 6) (by omega) (by decide) hK hG hη0 hη1
      hgood hM hz hc24 hvar hbase.order12⟩

#print axioms R_best
#print axioms distinct_floors
#print axioms R_best_kept
#print axioms mixture_orders
end BstLean.Part248
