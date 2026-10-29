import BstLean.Part90Defs

/-!
# Part 90, `core3`, `anchorNorm`, `anchorTA`

* `anchorTA`: Markov for `‖T[U_j]‖_F²`, whose mean is `‖T‖_F²`.
* `anchorNorm`: Chebyshev for the squared norm of one anchor row.
* `core3`: the failure bound from the interfaces at `d = k = 3`, with a sphere-step bound that
  holds for the anchors in a set `GU` of large probability.

No `sorry`, no `native_decide`, no `axiom`.
-/

namespace BstLean.Part90

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono varU Tens TSymm)
open BstLean.Part53 (radF53)
open BstLean.Part56 (UnitV kJ tauR polarPoint perpDir axialR axialS axialMeasure)
open BstLean.Part78 (nsq frobH zv)
open BstLean.Part80 (kA FeatOpA)
open BstLean.Part82 (T3 SymT frobT trT cfun aU3 HU3)
open BstLean.Part86
open BstLean.Part89 (Ybar SliceOpF)

theorem anchorTA (n : ℕ) (T : T3 n) (j : Fin (3 + 1)) (Mk : ℝ) (hMk : 0 < Mk) :
    stdGauss (Fin (3 + 1) × Fin n) {U | Mk * frobT T < frobH (TA T (fun i => U (j, i)))} ≤
      ENNReal.ofReal (1 / Mk) := by
  have hterm : ∀ i l : Fin n,
      Integrable (fun U : Fin (3 + 1) × Fin n → ℝ => (∑ k, T i l k * U (j, k)) ^ 2)
        (stdGauss (Fin (3 + 1) × Fin n)) ∧
      ∫ U : Fin (3 + 1) × Fin n → ℝ, (∑ k, T i l k * U (j, k)) ^ 2
        ∂stdGauss (Fin (3 + 1) × Fin n) = ∑ k, T i l k ^ 2 := fun i l =>
    BstLean.Part89.term_int (I := Fin (3 + 1)) (Matrix.of fun a k => T a l k) j i
  have hX : ∀ U : Fin (3 + 1) × Fin n → ℝ, frobH (TA T (fun i => U (j, i))) =
      ∑ i, ∑ l, (∑ k, T i l k * U (j, k)) ^ 2 := fun U => rfl
  have hnn : ∀ U : Fin (3 + 1) × Fin n → ℝ, 0 ≤ frobH (TA T (fun i => U (j, i))) :=
    fun U => BstLean.Part89.frobH_nonneg _
  have hi : ∀ i : Fin n, Integrable (fun U : Fin (3 + 1) × Fin n → ℝ =>
      ∑ l, (∑ k, T i l k * U (j, k)) ^ 2) (stdGauss (Fin (3 + 1) × Fin n)) :=
    fun i => integrable_finsetSum _ fun l _ => (hterm i l).1
  have hint : Integrable (fun U : Fin (3 + 1) × Fin n → ℝ => frobH (TA T (fun i => U (j, i))))
      (stdGauss (Fin (3 + 1) × Fin n)) := by
    simp_rw [hX]
    exact integrable_finsetSum _ fun i _ => hi i
  have hE : ∫ U : Fin (3 + 1) × Fin n → ℝ, frobH (TA T (fun i => U (j, i)))
      ∂stdGauss (Fin (3 + 1) × Fin n) = frobT T := by
    simp_rw [hX]
    rw [integral_finsetSum _ fun i _ => hi i]
    unfold frobT
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun l _ => (hterm i l).1]
    exact Finset.sum_congr rfl fun l _ => (hterm i l).2
  have hT0 : 0 ≤ frobT T := by
    unfold frobT
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _
  rcases hT0.lt_or_eq with hpos | hzero
  · have hm := BstLean.Part78.markov_gt (μ := stdGauss (Fin (3 + 1) × Fin n)) hnn hint
      (t := Mk * frobT T) (mul_pos hMk hpos) hE.le
    have he : frobT T / (Mk * frobT T) = 1 / Mk := by
      field_simp
    rw [he] at hm
    exact hm
  · have hz : ∀ i l k, T i l k = 0 := by
      intro i l k
      have h1 : T i l k ^ 2 ≤ frobT T := by
        unfold frobT
        refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ l, ∑ k, T i l k ^ 2)
          (fun i _ => Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
          (Finset.mem_univ i))
        refine le_trans ?_ (Finset.single_le_sum (f := fun l => ∑ k, T i l k ^ 2)
          (fun l _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ l))
        exact Finset.single_le_sum (f := fun k => T i l k ^ 2)
          (fun k _ => sq_nonneg _) (Finset.mem_univ k)
      rw [← hzero] at h1
      exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h1 (sq_nonneg _))
    have hempty : {U : Fin (3 + 1) × Fin n → ℝ |
        Mk * frobT T < frobH (TA T (fun i => U (j, i)))} = ∅ := by
      ext U
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [hX U, ← hzero]
      simp [hz]
    rw [hempty]
    simp

theorem anchorNorm (n : ℕ) (hn : 1 ≤ n) (j : Fin (3 + 1)) :
    stdGauss (Fin (3 + 1) × Fin n) {U | 11 / 10 * (n : ℝ) < ∑ i, U (j, i) ^ 2} ≤
      ENNReal.ofReal (200 / (n : ℝ)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinj : Function.Injective (fun i : Fin n => ((j, i) : Fin (3 + 1) × Fin n)) :=
    fun a b h => (Prod.mk.inj h).2
  have hmap := BstLean.Part29.stdGauss_map_restrict
    (fun i : Fin n => ((j, i) : Fin (3 + 1) × Fin n)) hinj
  have hmeasf : Measurable (fun z : Fin (3 + 1) × Fin n → ℝ =>
      z ∘ (fun i : Fin n => ((j, i) : Fin (3 + 1) × Fin n))) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have hSm : MeasurableSet {Z : Fin n → ℝ | 11 / 10 * (n : ℝ) < ∑ i, Z i ^ 2} :=
    measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2)
  have hpre : {U : Fin (3 + 1) × Fin n → ℝ | 11 / 10 * (n : ℝ) < ∑ i, U (j, i) ^ 2} =
      (fun z : Fin (3 + 1) × Fin n → ℝ =>
        z ∘ (fun i : Fin n => ((j, i) : Fin (3 + 1) × Fin n))) ⁻¹'
        {Z : Fin n → ℝ | 11 / 10 * (n : ℝ) < ∑ i, Z i ^ 2} := rfl
  rw [hpre, ← Measure.map_apply hmeasf hSm, hmap]
  have h := chi_tail_gen (Fin n) ((n : ℝ) / 10) (by positivity)
  rw [Fintype.card_fin] at h
  have he : 2 * (n : ℝ) / ((n : ℝ) / 10) ^ 2 = 200 / (n : ℝ) := by
    field_simp; ring
  rw [he] at h
  refine le_trans (measure_mono ?_) h
  intro Z hZ
  simp only [Set.mem_ofPred_eq] at hZ ⊢
  rw [lt_abs]
  left
  linarith

theorem core3 (m K : ℕ) (Ct A0 pU : ℝ) (t : ℝ) (v : Fin (m + 1) → ℝ)
    (ht : 0 ≤ t) (hv : UnitV v) (E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ) (hE : RotE v E)
    (hPol : PolarRed86 m 3 3 K) (hTail : TailIface86 (m + 1) 3 Ct)
    (f0 : ℝ) (T : Tens (m + 1)) (hT : TSymm 3 T)
    (GU : Set (Fin (3 + 1) × Fin (m + 1) → ℝ)) (hGU : MeasurableSet GU)
    (hGUp : stdGauss (Fin (3 + 1) × Fin (m + 1)) GUᶜ ≤ ENNReal.ofReal pU)
    (hA0 : 0 ≤ A0) (hpU : 0 ≤ pU)
    (hDW : 0 < DWr (m + 1) (JR (m + 1) 3))
    (hpt : ∀ (U : Fin (3 + 1) × Fin (m + 1) → ℝ) (W' : JR (m + 1) 3 × Fin (m + 1) → ℝ),
      U ∈ GU →
      |lam0 (DD (m + 1) 3) (DWr (m + 1) (JR (m + 1) 3)) U (radF53 W') ^ 2 - 1| ≤
          1 / (((m + 1 : ℕ) : ℝ)) →
      100 / 101 * DWr (m + 1) (JR (m + 1) 3) ≤ radF53 W' ^ 2 →
      stdGauss (JR (m + 1) 3 × Fin (m + 1))
          (badSet86 (modRK m 3 t v E) (gqRK m 3 K t v E)
            (PU 3 f0 T U (Real.sqrt (∑ a, U a ^ 2 + radF53 W' ^ 2))
              (1 / Real.sqrt (DD (m + 1) 3)))
            (lam0 (DD (m + 1) 3) (DWr (m + 1) (JR (m + 1) 3)) U (radF53 W'))) ≤
        ENNReal.ofReal A0) :
    stdGauss (CoefIdxD (m + 1) 3) (SphereFail86 (m + 1) 3 3 K t v f0 T) ≤
      ENNReal.ofReal A0 + ENNReal.ofReal pU + ENNReal.ofReal (Ct / ((m + 1 : ℕ) : ℝ)) +
        ENNReal.ofReal (20808 / DWr (m + 1) (JR (m + 1) 3)) := by
  classical
  set S : Set ((Fin (3 + 1) × Fin (m + 1) → ℝ) × (JR (m + 1) 3 × Fin (m + 1) → ℝ)) :=
    {p | 1 / (((m + 1 : ℕ) : ℝ)) <
      |lam0 (DD (m + 1) 3) (DWr (m + 1) (JR (m + 1) 3)) p.1 (radF53 p.2) ^ 2 - 1|} with hS
  set S2 : Set (JR (m + 1) 3 × Fin (m + 1) → ℝ) :=
    {W' | radF53 W' ^ 2 < 100 / 101 * DWr (m + 1) (JR (m + 1) 3)} with hS2
  have hS2m : MeasurableSet S2 :=
    measurableSet_lt ((BstLean.Part53.measurable_radF).pow_const 2) measurable_const
  set g : (Fin (3 + 1) × Fin (m + 1) → ℝ) → ℝ≥0∞ :=
    fun U => ENNReal.ofReal A0 + GUᶜ.indicator (fun _ => (1 : ℝ≥0∞)) U with hg
  have hgmeas : Measurable g :=
    (Measurable.indicator (f := fun _ => (1 : ℝ≥0∞)) measurable_const hGU.compl).const_add _
  have hgI : ∫⁻ U, g U ∂stdGauss (Fin (3 + 1) × Fin (m + 1)) ≤
      ENNReal.ofReal A0 + ENNReal.ofReal pU := by
    rw [hg, lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_indicator hGU.compl]
    simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
      one_mul]
    exact add_le_add le_rfl hGUp
  have hpt' : ∀ (U : Fin (3 + 1) × Fin (m + 1) → ℝ) (W' : JR (m + 1) 3 × Fin (m + 1) → ℝ),
      stdGauss (JR (m + 1) 3 × Fin (m + 1))
          (badSet86 (modRK m 3 t v E) (gqRK m 3 K t v E)
            (PU 3 f0 T U (Real.sqrt (∑ a, U a ^ 2 + radF53 W' ^ 2))
              (1 / Real.sqrt (DD (m + 1) 3)))
            (lam0 (DD (m + 1) 3) (DWr (m + 1) (JR (m + 1) 3)) U (radF53 W'))) ≤
        (g U + S2.indicator (fun _ => (1 : ℝ≥0∞)) W') +
          S.indicator (fun _ => (1 : ℝ≥0∞)) (U, W') := by
    intro U W'
    by_cases h : (U, W') ∈ S
    · rw [Set.indicator_of_mem h]
      exact (prob_le_one).trans le_add_self
    by_cases h2 : W' ∈ S2
    · rw [Set.indicator_of_mem h2]
      exact (prob_le_one).trans (le_trans le_add_self le_self_add)
    by_cases h3 : U ∈ GUᶜ
    · have : (1 : ℝ≥0∞) ≤ g U := by
        rw [hg]; simp only; rw [Set.indicator_of_mem h3]; exact le_add_self
      exact (prob_le_one).trans (le_trans this (le_trans le_self_add le_self_add))
    · have hgU : g U = ENNReal.ofReal A0 := by
        rw [hg]; simp only; rw [Set.indicator_of_notMem h3, add_zero]
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h2, add_zero, add_zero, hgU]
      have h' : |lam0 (DD (m + 1) 3) (DWr (m + 1) (JR (m + 1) 3)) U (radF53 W') ^ 2 - 1| ≤
          1 / (((m + 1 : ℕ) : ℝ)) := by
        simpa [hS, not_lt] using h
      have h2' : 100 / 101 * DWr (m + 1) (JR (m + 1) 3) ≤ radF53 W' ^ 2 := by
        simpa [hS2, not_lt] using h2
      exact hpt U W' (by simpa using h3) h' h2'
  refine (hPol t v ht hv E hE f0 T hT).trans ?_
  refine (lintegral_mono fun U => lintegral_mono fun W' => hpt' U W').trans ?_
  have e1 : ∀ U : Fin (3 + 1) × Fin (m + 1) → ℝ, ∫⁻ W' : JR (m + 1) 3 × Fin (m + 1) → ℝ,
      ((g U + S2.indicator (fun _ => (1 : ℝ≥0∞)) W') +
        S.indicator (fun _ => (1 : ℝ≥0∞)) (U, W'))
      ∂stdGauss (JR (m + 1) 3 × Fin (m + 1)) =
      (g U + stdGauss (JR (m + 1) 3 × Fin (m + 1)) S2) +
        ∫⁻ W' : JR (m + 1) 3 × Fin (m + 1) → ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) (U, W')
          ∂stdGauss (JR (m + 1) 3 × Fin (m + 1)) := by
    intro U
    have hm1 : Measurable (fun W' : JR (m + 1) 3 × Fin (m + 1) → ℝ =>
        g U + S2.indicator (fun _ => (1 : ℝ≥0∞)) W') :=
      (Measurable.indicator (f := fun _ => (1 : ℝ≥0∞)) measurable_const hS2m).const_add _
    rw [lintegral_add_left hm1, lintegral_add_left measurable_const, lintegral_const,
      measure_univ, mul_one, lintegral_indicator hS2m]
    simp
  simp_rw [e1]
  have hm2 : Measurable (fun U : Fin (3 + 1) × Fin (m + 1) → ℝ =>
      g U + stdGauss (JR (m + 1) 3 × Fin (m + 1)) S2) :=
    hgmeas.add measurable_const
  rw [lintegral_add_left hm2, lintegral_add_left hgmeas, lintegral_const, measure_univ, mul_one]
  have hrad : stdGauss (JR (m + 1) 3 × Fin (m + 1)) S2 ≤
      ENNReal.ofReal (20808 / DWr (m + 1) (JR (m + 1) 3)) :=
    BstLean.Part89.rad_tail (JR (m + 1) 3 × Fin (m + 1)) hDW
  calc _ ≤ (ENNReal.ofReal A0 + ENNReal.ofReal pU) +
        ENNReal.ofReal (20808 / DWr (m + 1) (JR (m + 1) 3)) +
        ENNReal.ofReal (Ct / ((m + 1 : ℕ) : ℝ)) :=
        add_le_add (add_le_add hgI hrad) hTail
    _ = _ := by ring

end BstLean.Part90

#print axioms BstLean.Part90.anchorTA
#print axioms BstLean.Part90.anchorNorm
#print axioms BstLean.Part90.core3
