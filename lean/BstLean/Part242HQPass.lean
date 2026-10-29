import BstLean.Part180HQFl
import BstLean.Part242HQNorm

/-! The paper HQ price uses the original normalized good transverse distribution. -/
namespace BstLean.Part242
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157 BstLean.Part161 BstLean.Part162
variable {n : ℕ}

/-- The original conditional good mixture receives the coefficient-six HQ price. -/
theorem root_le_hq_paper (D : Design n) (t : ℝ) (c : Ret n) (d : SplitData n) (a : Ix n)
    (hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1) (hS0 : 0 < d.S0 a) {ε₀ δ₀ : ℝ}
    (hε0 : 0 ≤ ε₀) (hε₀ : ε₀ < 1) (hδ0 : 0 ≤ δ₀)
    (hw : ∀ v ∈ slice d a, |sA D c a v / d.S0 a - 1| ≤ ε₀ ∧ |lA D c a v - d.lam0 a| ≤ δ₀)
    (hmδ : ∫ v in slice d a, (lA D c a v - d.lam0 a) ∂stdGauss (Fin (n - 1)) = 0)
    (hmε : ∫ v in slice d a, (sA D c a v / d.S0 a - 1) ∂stdGauss (Fin (n - 1)) = 0) :
    (sqrt (goodMean (stdGauss (Fin (n - 1))) d.good (pLat D t c) a) -
      sqrt (q0Lat t c d a)) ^ 2 ≤ chiK D c d a / 4 +
        6 * BstLean.Part207.hqL n ε₀ (condMom d (epsF D c d) 2 a)
          (condMom d (delF D c d) 2 a) ^ 3
:= by
  classical
  set ν := stdGauss (Fin (n - 1)) with hν
  set s := slice d a with hs
  have ms : MeasurableSet s := measurableSet_slice d a
  set β := removed ν d.good a with hβd
  set m := 1 - β with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hνs : ν.real s = m := by
    have h1 : β = ν.real sᶜ := rfl
    rw [hm, h1, measureReal_compl ms, probReal_univ]
    ring
  set k : ℝ≥0∞ := (ENNReal.ofReal m)⁻¹ with hk
  have hkr : k.toReal = m⁻¹ := by
    rw [hk, ENNReal.toReal_inv, ENNReal.toReal_ofReal hm0.le]
  set piG : Measure (Fin (n - 1) → ℝ) := k • ν.restrict s with hpiG
  have hνs' : ν s = ENNReal.ofReal m := by
    rw [← hνs, ofReal_measureReal (measure_ne_top _ _)]
  have hprob : IsProbabilityMeasure piG := by
    constructor
    rw [hpiG, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      hνs', smul_eq_mul, hk, ENNReal.inv_mul_cancel (by simpa using hm0) ENNReal.ofReal_ne_top]
  -- the clipped parameters
  set l' : (Fin (n - 1) → ℝ) → ℝ := s.piecewise (lA D c a) (fun _ => d.lam0 a) with hl'
  set S' : (Fin (n - 1) → ℝ) → ℝ := s.piecewise (sA D c a) (fun _ => d.S0 a) with hS'
  have ml : Measurable (lA D c a) := measurable_lA_left D c a
  have mS : Measurable (sA D c a) := measurable_sA_left D c a
  have ml' : Measurable l' := ml.piecewise ms measurable_const
  have mS' : Measurable S' := mS.piecewise ms measurable_const
  have hwS : ∀ v, |S' v / d.S0 a - 1| ≤ ε₀ := fun v => by
    by_cases hv : v ∈ s
    · simp only [hS', Set.piecewise_eq_of_mem _ _ _ hv]; exact (hw v hv).1
    · simp only [hS', Set.piecewise_eq_of_notMem _ _ _ hv, div_self hS0.ne', sub_self,
        abs_zero]; exact hε0
  have hwl : ∀ v, |l' v - d.lam0 a| ≤ δ₀ := fun v => by
    by_cases hv : v ∈ s
    · simp only [hl', Set.piecewise_eq_of_mem _ _ _ hv]; exact (hw v hv).2
    · simp only [hl', Set.piecewise_eq_of_notMem _ _ _ hv, sub_self, abs_zero]; exact hδ0
  have hmδ' : ∫ v, (l' v - d.lam0 a) ∂piG = 0 := by
    rw [hpiG, integral_smul_measure, ← integral_indicator ms]
    have : ∫ v, s.indicator (fun v => l' v - d.lam0 a) v ∂ν = ∫ v in s, (lA D c a v - d.lam0 a) ∂ν := by
      rw [← integral_indicator ms]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      by_cases hv : v ∈ s
      · simp only [Set.indicator_of_mem hv, hl', Set.piecewise_eq_of_mem _ _ _ hv]
      · simp only [Set.indicator_of_notMem hv]
    rw [this, hmδ, smul_zero]
  have hmε' : ∫ v, (S' v / d.S0 a - 1) ∂piG = 0 := by
    rw [hpiG, integral_smul_measure, ← integral_indicator ms]
    have : ∫ v, s.indicator (fun v => S' v / d.S0 a - 1) v ∂ν =
        ∫ v in s, (sA D c a v / d.S0 a - 1) ∂ν := by
      rw [← integral_indicator ms]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      by_cases hv : v ∈ s
      · simp only [Set.indicator_of_mem hv, hS', Set.piecewise_eq_of_mem _ _ _ hv]
      · simp only [Set.indicator_of_notMem hv]
    rw [this, hmε, smul_zero]
  have hmain := BstLean.Part207.mix_root_hq_paper piG c.2.1.2
    (measurableSet_clsSet c t) hS0 ml' mS' hε₀ hwS hwl hmδ' hmε'
  -- the conditional moments
  have hX : ∫ v, (S' v / d.S0 a - 1) ^ 2 ∂piG = condMom d (epsF D c d) 2 a := by
    unfold condMom
    rw [hpiG, integral_smul_measure, hkr, ← integral_indicator ms, smul_eq_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    by_cases hv : v ∈ s
    · simp only [Set.indicator_of_mem hv, hS', Set.piecewise_eq_of_mem _ _ _ hv, epsF, eG, sq_abs,
        Set.indicator_of_mem (show v ∈ slice d a from hv)]
    · simp only [Set.indicator_of_notMem hv, epsF, eG, Set.indicator_of_notMem (show v ∉ slice d a from hv)]; norm_num
  have hY : ∫ v, normSq c.2.1.2 / d.S0 a * (l' v - d.lam0 a) ^ 2 ∂piG =
      condMom d (delF D c d) 2 a := by
    unfold condMom
    rw [hpiG, integral_smul_measure, hkr, ← integral_indicator ms, smul_eq_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    by_cases hv : v ∈ s
    · simp only [Set.indicator_of_mem hv, hl', Set.piecewise_eq_of_mem _ _ _ hv, delF, dG,
        Set.indicator_of_mem (show v ∈ slice d a from hv)]
      rw [abs_mul, mul_pow, sq_abs, sq_abs, Real.sq_sqrt (div_nonneg (normSq_nonneg _) hS0.le)]
    · simp only [Set.indicator_of_notMem hv, delF, dG, Set.indicator_of_notMem (show v ∉ slice d a from hv)]; norm_num
  rw [hX, hY] at hmain
  -- the good-set mean
  have hA : ∫ v, gP (clsSet c t) (l' v • c.2.1.2) (S' v) ∂piG =
      goodMean ν d.good (pLat D t c) a := by
    rw [hpiG, integral_smul_measure, hkr, ← integral_indicator ms]  
    unfold goodMean
    rw [smul_eq_mul, inv_mul_eq_div]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    by_cases hv : v ∈ s
    · have hv' : (a, v) ∈ d.good := hv
      simp only [Set.indicator_of_mem hv, Set.indicator_of_mem hv', hl', hS',
        Set.piecewise_eq_of_mem _ _ _ hv]
      rfl
    · have hv' : (a, v) ∉ d.good := hv
      simp only [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv']
  rw [hA] at hmain
  refine hmain.trans (le_of_eq ?_)
  congr 2
  -- the two-copy integral
  have hprod : piG.prod piG = (k * k) • (ν.prod ν).restrict (s ×ˢ s) := by
    rw [← Measure.prod_restrict]
    refine Measure.prod_eq fun A A' hA hA' => ?_
    rw [Measure.smul_apply, Measure.prod_prod, smul_eq_mul, hpiG, Measure.smul_apply,
      Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [hprod, integral_smul_measure, ← integral_indicator (ms.prod ms)]
  unfold chiK kChiInt
  rw [ENNReal.toReal_mul, hkr]
  congr 1
  rw [smul_eq_mul, sq]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  by_cases h1 : w.1 ∈ s
  · by_cases h2 : w.2 ∈ s
    · have h12 : w ∈ s ×ˢ s := ⟨h1, h2⟩
      simp only [Set.indicator_of_mem h12, Set.indicator_of_mem (show w.1 ∈ slice d a from h1),
        Set.indicator_of_mem (show w.2 ∈ slice d a from h2),
        hl', hS', Set.piecewise_eq_of_mem _ _ _ h1, Set.piecewise_eq_of_mem _ _ _ h2,
        Pi.one_apply, one_mul]
    · have h12 : w ∉ s ×ˢ s := fun h => h2 h.2
      simp only [Set.indicator_of_notMem h12,
        Set.indicator_of_notMem (show w.2 ∉ slice d a from h2), mul_zero, zero_mul]
  · have h12 : w ∉ s ×ˢ s := fun h => h1 h.1
    simp only [Set.indicator_of_notMem h12,
      Set.indicator_of_notMem (show w.1 ∉ slice d a from h1), zero_mul]



end BstLean.Part242
