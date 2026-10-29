import BstLean.Part180HQ

/-!
# Part 180 (file `HQFl`): Lemma HQ in the fluctuation root

No proof is left open; no `native_decide` or `axiom` is used.

* `root_le_hq`: Lemma HQ at one kept latitude index (the good-set mixture against the good-set
  reference), with the conditional moments `X = condMom ε 2`, `Y = condMom (a_c δ) 2`.
* `int_chiK_le`: `∫_K chiK ≤ 𝒞` (the middle part of Part 162's `fluct_of_moments`).
* `int_cube_le`, `condMom2_pow_le`, `int_cub_le`: `∫_K (K̂³/λ² + Ŷ/((1 − ε₀)²(1 − λ)²)) ≤ cubP`.
* `fluct_of_moments_hq`: Part 162's `fluct_of_moments` with the root `√(𝒞/4 + (3/4)cubP)`; its
  conclusion is `FLUCT_hyp` (Part 161), not `FLUCT_chi_hyp`.
* `fluct_paper_hq`, `fluct_paper_mom_hq`, **`fluct_of_latMom_hq`**: Part 162's `fluct_paper`,
  `fluct_paper_mom`, `fluct_of_latMom` with the Lemma HQ root (`rootFLH`, file `Def`).
-/

namespace BstLean.Part180

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157 BstLean.Part161 BstLean.Part162

variable {n : ℕ}

/-- **Lemma HQ at one kept index**: the root of the classifier event against the good-set
reference is at most `chiK/4 + (3/4)·(K̂³/λ² + Ŷ/(1 − λ)²)`, with the conditional moments
`X = condMom ε 2`, `Y = condMom (a_c δ) 2` of the good slice. -/
theorem root_le_hq (D : Design n) (t : ℝ) (c : Ret n) (d : SplitData n) (a : Ix n)
    (hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1) (hS0 : 0 < d.S0 a) {ε₀ δ₀ : ℝ}
    (hε0 : 0 ≤ ε₀) (hε₀ : ε₀ < 1) (hδ0 : 0 ≤ δ₀)
    (hw : ∀ v ∈ slice d a, |sA D c a v / d.S0 a - 1| ≤ ε₀ ∧ |lA D c a v - d.lam0 a| ≤ δ₀)
    (hmδ : ∫ v in slice d a, (lA D c a v - d.lam0 a) ∂stdGauss (Fin (n - 1)) = 0)
    (hmε : ∫ v in slice d a, (sA D c a v / d.S0 a - 1) ∂stdGauss (Fin (n - 1)) = 0)
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    (√(goodMean (stdGauss (Fin (n - 1))) d.good (pLat D t c) a) - √(q0Lat t c d a)) ^ 2 ≤
      chiK D c d a / 4 + 3 / 4 *
        ((n * ((1 + 3 * ε₀) / (4 * (1 - ε₀))) * condMom d (epsF D c d) 2 a +
          condMom d (delF D c d) 2 a / (2 * (1 - ε₀))) ^ 3 / lam ^ 2 +
        (n * condMom d (epsF D c d) 2 a ^ 2 +
          2 * condMom d (epsF D c d) 2 a * condMom d (delF D c d) 2 a) /
          ((1 - ε₀) ^ 2 * (1 - lam) ^ 2)) := by
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
  have hmain := mix_root_hq piG c.2.1.2 (measurableSet_clsSet c t) hS0 ml' mS' hε₀ hwS hwl
    hmδ' hmε' hl0 hl1
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


/-- **The integrated chi-square price** (the middle part of Part 162's `fluct_of_moments`):
`∫_K chiK ≤ 𝒞` from the conditional moments. -/
theorem int_chiK_le (D : Design n) (c : Ret n) (d : SplitData n)
    {ε₀ δ₀ L slow : ℝ} (hε0 : 0 ≤ ε₀) (hε₀ : ε₀ < 1) (hδ0 : 0 ≤ δ₀) (hL : 0 ≤ L)
    (hslow : 0 < slow) (hcA : 0 < normSq c.2.1.2)
    (hwin : ∀ a ∈ keptIx D c d, slow ≤ d.S0 a ∧ ∀ v ∈ slice d a,
      |sA D c a v / d.S0 a - 1| ≤ ε₀ ∧ |lA D c a v - d.lam0 a| ≤ δ₀ ∧
      normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2 ≤ L ^ 2)
    (hcent : ∀ a ∈ keptIx D c d,
      ∫ v in slice d a, (lA D c a v - d.lam0 a) ∂stdGauss (Fin (n - 1)) = 0 ∧
      ∫ v in slice d a, (sA D c a v / d.S0 a - 1) ∂stdGauss (Fin (n - 1)) = 0)
    {A Dm e4 d4 e6 d6 : ℝ} (hA : 0 ≤ A) (hDm : 0 ≤ Dm) (he4 : 0 ≤ e4) (hd4 : 0 ≤ d4)
    (he6 : 0 ≤ e6) (hd6 : 0 ≤ d6)
    (IA : ∫ a in keptIx D c d, condMom d (epsF D c d) 2 a ^ 2 ∂muI n ≤ A ^ 2)
    (ID : ∫ a in keptIx D c d, condMom d (delF D c d) 2 a ^ 2 ∂muI n ≤ Dm ^ 2)
    (Ie4 : ∫ a in keptIx D c d, condMom d (epsF D c d) 8 a ∂muI n ≤ e4 ^ 8)
    (Id4 : ∫ a in keptIx D c d, condMom d (delF D c d) 8 a ∂muI n ≤ d4 ^ 8)
    (Ie6 : ∫ a in keptIx D c d, condMom d (epsF D c d) 12 a ∂muI n ≤ e6 ^ 12)
    (Id6 : ∫ a in keptIx D c d, condMom d (delF D c d) 12 a ∂muI n ≤ d6 ^ 12) :
    ∫ a in keptIx D c d, chiK D c d a ∂muI n ≤ priceC (1 - ε₀ ^ 2)⁻¹ n L ε₀
        (exp ((1 - ε₀ ^ 2)⁻¹ * (n * ε₀ ^ 2 / 2 + L ^ 2 * (1 + ε₀)))) A Dm e4 d4 e6 d6 := by
  set ν := stdGauss (Fin (n - 1))
  set K := keptIx D c d with hKd
  have mK : MeasurableSet K :=
    measurableSet_keptSet ν d.mgood (measurableSet_bulkIx D c) d.eta
  have hKβ : ∀ a ∈ K, removed ν d.good a < 1 := fun a ha => lt_of_le_of_lt ha.2 d.eta_lt
  set κ := (1 - ε₀ ^ 2)⁻¹ with hκ
  have hκ0 : 0 ≤ κ := inv_nonneg.mpr (by nlinarith)
  set E := exp ((1 - ε₀ ^ 2)⁻¹ * (n * ε₀ ^ 2 / 2 + L ^ 2 * (1 + ε₀))) with hE
  -- the two fields
  have hvE : ∀ a v, v ∉ slice d a → epsF D c d a v = 0 := fun a v hv => by
    simp only [epsF, eG, Set.indicator_of_notMem hv]
  have hvD : ∀ a v, v ∉ slice d a → delF D c d a v = 0 := fun a v hv => by
    simp only [delF, dG, Set.indicator_of_notMem hv, mul_zero]
  have mE := measurable_epsF D c d
  have mD := measurable_delF D c d
  have hbE : ∀ a ∈ K, ∀ v, |epsF D c d a v| ≤ ε₀ := fun a ha v => by
    by_cases hv : v ∈ slice d a
    · simp only [epsF, eG, Set.indicator_of_mem hv]; exact ((hwin a ha).2 v hv).1
    · rw [hvE a v hv, abs_zero]; exact hε0
  have hbD : ∀ a ∈ K, ∀ v, |delF D c d a v| ≤ L := fun a ha v => by
    by_cases hv : v ∈ slice d a
    · simp only [delF, dG, Set.indicator_of_mem hv]
      have h := ((hwin a ha).2 v hv).2.2
      have hS : 0 < d.S0 a := lt_of_lt_of_le hslow (hwin a ha).1
      have h2 : √(normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2) ≤ √(L ^ 2) :=
        Real.sqrt_le_sqrt h
      rwa [Real.sqrt_mul (div_nonneg (normSq_nonneg _) hS.le), Real.sqrt_sq_eq_abs,
        Real.sqrt_sq hL, ← abs_of_nonneg (Real.sqrt_nonneg (normSq c.2.1.2 / d.S0 a)),
        ← abs_mul] at h2
    · rw [hvD a v hv, abs_zero]; exact hL
  -- the scales
  set xs : (Ix n → (Fin (n - 1) → ℝ) → ℝ) → ℕ → Ix n → ℝ :=
    fun F k a => condMom d F k a ^ ((k : ℝ)⁻¹) with hxs
  set xK : (Ix n → (Fin (n - 1) → ℝ) → ℝ) → ℕ → Ix n → ℝ :=
    fun F k => K.indicator (xs F k) with hxK
  set g : Ix n → ℝ := fun a => sixF κ n L ε₀ E (xs (epsF D c d) 2 a) (xs (delF D c d) 2 a)
    (xs (epsF D c d) 4 a) (xs (delF D c d) 4 a) (xs (epsF D c d) 6 a) (xs (delF D c d) 6 a)
    with hg
  -- per index
  have hpt : ∀ a ∈ K, chiK D c d a ≤ g a := fun a ha => by
    have hS : 0 < d.S0 a := lt_of_lt_of_le hslow (hwin a ha).1
    have h := chiK_le_sixF D c d (hKβ a ha) hS hcA hε0 hε₀ hL
      (fun v hv => ⟨((hwin a ha).2 v hv).1, ((hwin a ha).2 v hv).2.2⟩) (hcent a ha).1
      (hcent a ha).2
    have eE : ∀ k : ℕ, k ≠ 0 → momN (gMeas d a) k (eG D c d a) = xs (epsF D c d) k a :=
      fun k hk => momN_eq_condMom d hvE (hKβ a ha) hk
    have eD : ∀ k : ℕ, k ≠ 0 → momN (gMeas d a) k
        (fun v => √(normSq c.2.1.2 / d.S0 a) * dG D c d a v) = xs (delF D c d) k a :=
      fun k hk => momN_eq_condMom d hvD (hKβ a ha) hk
    rw [eE 2 two_ne_zero, eE 4 (by norm_num), eE 6 (by norm_num), eD 2 two_ne_zero,
      eD 4 (by norm_num), eD 6 (by norm_num)] at h
    exact h
  -- integrability
  have iC : IntegrableOn (chiK D c d) K (muI n) := by
    set Mc := (√(1 - ε₀ ^ 2))⁻¹ ^ n *
      exp ((1 + ε₀) * (normSq c.2.1.2 / slow) * δ₀ ^ 2 / (1 - ε₀ ^ 2))
    refine Integrable.of_bound (measurable_chiK D c d).aestronglyMeasurable (Mc + 1)
      (ae_restrict_of_forall_mem mK fun a ha => ?_)
    obtain ⟨b1, b2⟩ := chiK_bounds D c d hε0 hε₀ hslow a (hKβ a ha) (hwin a ha).1
      (fun v hv => ⟨((hwin a ha).2 v hv).1, ((hwin a ha).2 v hv).2.1⟩)
    have hM0 : 0 ≤ Mc :=
      mul_nonneg (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _) (exp_pos _).le
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  set M := max ε₀ L with hM
  have bE : ∀ k : ℕ, k ≠ 0 → ∀ a, 0 ≤ xK (epsF D c d) k a ∧ xK (epsF D c d) k a ≤ M :=
    fun k hk a => by
      obtain ⟨h0, h1⟩ := field_bound d hKβ mE hvE hε0 hbE hk a
      exact ⟨h0, h1.trans (le_max_left _ _)⟩
  have bD : ∀ k : ℕ, k ≠ 0 → ∀ a, 0 ≤ xK (delF D c d) k a ∧ xK (delF D c d) k a ≤ M :=
    fun k hk a => by
      obtain ⟨h0, h1⟩ := field_bound d hKβ mD hvD hL hbD hk a
      exact ⟨h0, h1.trans (le_max_right _ _)⟩
  have mxs : ∀ {F : Ix n → (Fin (n - 1) → ℝ) → ℝ}, Measurable (Function.uncurry F) →
      ∀ k, Measurable (xs F k) := fun hF k => (measurable_condMom d hF k).pow_const _
  have mxK : ∀ {F : Ix n → (Fin (n - 1) → ℝ) → ℝ}, Measurable (Function.uncurry F) →
      ∀ k, Measurable (xK F k) := fun hF k => (mxs hF k).indicator mK
  have hε1 : 0 ≤ 1 + ε₀ := by linarith
  have hE0 : 0 ≤ E := (exp_pos _).le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have iG : IntegrableOn g K (muI n) := by
    have mg : Measurable g := by
      simp only [hg]
      unfold sixF tK
      have := mxs mE 2; have := mxs mD 2; have := mxs mE 4; have := mxs mD 4
      have := mxs mE 6; have := mxs mD 6
      fun_prop
    refine Integrable.of_bound mg.aestronglyMeasurable (sixF κ n L ε₀ E M M M M M M)
      (ae_restrict_of_forall_mem mK fun a ha => ?_)
    have q : ∀ (F : Ix n → (Fin (n - 1) → ℝ) → ℝ) k, xK F k a = xs F k a := fun F k => by
      simp only [hxK, Set.indicator_of_mem ha]
    have s := sixF_mono hκ0 hn0 hL hε1 hE0 (q (epsF D c d) 2 ▸ bE 2 two_ne_zero a)
      (q (delF D c d) 2 ▸ bD 2 two_ne_zero a) (q (epsF D c d) 4 ▸ bE 4 (by norm_num) a)
      (q (delF D c d) 4 ▸ bD 4 (by norm_num) a) (q (epsF D c d) 6 ▸ bE 6 (by norm_num) a)
      (q (delF D c d) 6 ▸ bD 6 (by norm_num) a)
    rw [Real.norm_eq_abs, abs_of_nonneg s.1]
    exact s.2
  refine (setIntegral_mono_on iC iG mK hpt).trans ?_
  have hind : K.indicator g = fun a => sixF κ n L ε₀ E (xK (epsF D c d) 2 a) (xK (delF D c d) 2 a)
      (xK (epsF D c d) 4 a) (xK (delF D c d) 4 a) (xK (epsF D c d) 6 a) (xK (delF D c d) 6 a) := by
    funext a
    by_cases ha : a ∈ K
    · simp only [hxK, Set.indicator_of_mem ha, hg]
    · simp only [hxK, Set.indicator_of_notMem ha, sixF_zero]
  rw [← integral_indicator mK, hind]
  have J2E := field_int_sq d mK hKβ mE hvE two_ne_zero IA
  have J2D := field_int_sq d mK hKβ mD hvD two_ne_zero ID
  have J4E := field_int d mK hKβ mE hvE hbE (k := 4) (by norm_num) Ie4
  have J4D := field_int d mK hKβ mD hvD hbD (k := 4) (by norm_num) Id4
  have J6E := field_int d mK hKβ mE hvE hbE (k := 6) (by norm_num) Ie6
  have J6D := field_int d mK hKβ mD hvD hbD (k := 6) (by norm_num) Id6
  exact int_sixF (muI n) (mxK mE 2) (mxK mD 2) (mxK mE 4) (mxK mD 4) (mxK mE 6) (mxK mD 6)
    (bE 2 two_ne_zero) (bD 2 two_ne_zero) (bE 4 (by norm_num)) (bD 4 (by norm_num))
    (bE 6 (by norm_num)) (bD 6 (by norm_num)) hκ0 hn0 hL hε1 hE0 hA hDm he4 hd4 he6 hd6
    J2E J2D J4E J4D J6E J6D



end BstLean.Part180

namespace BstLean.Part180

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157 BstLean.Part161 BstLean.Part162

section holder
variable {α : Type*} [MeasurableSpace α]

/-- `∫ f³ ≤ A^{3/2} e³` from `∫ f² ≤ A²`, `∫ f⁶ ≤ e¹²` (two Cauchy–Schwarz steps), for a bounded
measurable `f ≥ 0` and a probability measure. -/
lemma int_cube_le (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f) {M : ℝ}
    (hb : ∀ a, 0 ≤ f a ∧ f a ≤ M) {A e : ℝ} (hA : 0 ≤ A) (he : 0 ≤ e)
    (h2 : ∫ a, f a ^ 2 ∂μ ≤ A ^ 2) (h6 : ∫ a, f a ^ 6 ∂μ ≤ e ^ 12) :
    ∫ a, f a ^ 3 ∂μ ≤ A * √A * e ^ 3 := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  have hM : 0 ≤ M := (hb (Classical.arbitrary α)).1.trans (hb _).2
  have ip : ∀ k : ℕ, Integrable (fun a => f a ^ k) μ := fun k =>
    Integrable.of_bound (hf.pow_const k).aestronglyMeasurable (M ^ k)
      (Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hb a).1 k)]
        exact pow_le_pow_left₀ (hb a).1 (hb a).2 k)
  have ipp : ∀ k j : ℕ, Integrable (fun a => (f a ^ k) ^ j) μ := fun k j =>
    (ip (k * j)).congr (Filter.Eventually.of_forall fun a => by simp only [pow_mul])
  have ipm : ∀ k j : ℕ, Integrable (fun a => f a ^ k * f a ^ j) μ := fun k j =>
    (ip (k + j)).congr (Filter.Eventually.of_forall fun a => by simp only [pow_add])
  have c1 : (∫ a, f a ^ 3 ∂μ) ^ 2 ≤ (∫ a, f a ^ 2 ∂μ) * ∫ a, f a ^ 4 ∂μ := by
    have h := BstLean.Part138.cs_sq μ (ipp 1 2) (ipp 2 2) (ipm 1 2)
    have e1 : ∀ a, f a ^ 1 * f a ^ 2 = f a ^ 3 := fun a => by ring
    have e2 : ∀ a, (f a ^ 1) ^ 2 = f a ^ 2 := fun a => by ring
    have e3 : ∀ a, (f a ^ 2) ^ 2 = f a ^ 4 := fun a => by ring
    simp only [e1, e2, e3] at h; exact h
  have c2 : (∫ a, f a ^ 4 ∂μ) ^ 2 ≤ (∫ a, f a ^ 2 ∂μ) * ∫ a, f a ^ 6 ∂μ := by
    have h := BstLean.Part138.cs_sq μ (ipp 1 2) (ipp 3 2) (ipm 1 3)
    have e1 : ∀ a, f a ^ 1 * f a ^ 3 = f a ^ 4 := fun a => by ring
    have e2 : ∀ a, (f a ^ 1) ^ 2 = f a ^ 2 := fun a => by ring
    have e3 : ∀ a, (f a ^ 3) ^ 2 = f a ^ 6 := fun a => by ring
    simp only [e1, e2, e3] at h; exact h
  have i2 : 0 ≤ ∫ a, f a ^ 2 ∂μ := integral_nonneg fun a => pow_nonneg (hb a).1 _
  have i4 : 0 ≤ ∫ a, f a ^ 4 ∂μ := integral_nonneg fun a => pow_nonneg (hb a).1 _
  have i6 : 0 ≤ ∫ a, f a ^ 6 ∂μ := integral_nonneg fun a => pow_nonneg (hb a).1 _
  have i3 : 0 ≤ ∫ a, f a ^ 3 ∂μ := integral_nonneg fun a => pow_nonneg (hb a).1 _
  -- `∫ f⁴ ≤ A e⁶`
  have h4 : (∫ a, f a ^ 4 ∂μ) ^ 2 ≤ (A * e ^ 6) ^ 2 := by
    calc (∫ a, f a ^ 4 ∂μ) ^ 2 ≤ (∫ a, f a ^ 2 ∂μ) * ∫ a, f a ^ 6 ∂μ := c2
      _ ≤ A ^ 2 * e ^ 12 := mul_le_mul h2 h6 i6 (sq_nonneg _)
      _ = (A * e ^ 6) ^ 2 := by ring
  have h4' : ∫ a, f a ^ 4 ∂μ ≤ A * e ^ 6 := (pow_le_pow_iff_left₀ i4 (by positivity) two_ne_zero).mp h4
  have h3 : (∫ a, f a ^ 3 ∂μ) ^ 2 ≤ (A * √A * e ^ 3) ^ 2 := by
    calc (∫ a, f a ^ 3 ∂μ) ^ 2 ≤ (∫ a, f a ^ 2 ∂μ) * ∫ a, f a ^ 4 ∂μ := c1
      _ ≤ A ^ 2 * (A * e ^ 6) := mul_le_mul h2 h4' i4 (sq_nonneg _)
      _ = (A * √A * e ^ 3) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hA]; ring
  exact (pow_le_pow_iff_left₀ i3 (by positivity) two_ne_zero).mp h3

end holder


variable {n : ℕ}

/-- The conditional second moment to a power is at most the conditional moment of the
corresponding order (Jensen on the normalized good slice). -/
lemma condMom2_pow_le (d : SplitData n) {F : Ix n → (Fin (n - 1) → ℝ) → ℝ}
    (hF : Measurable (Function.uncurry F)) (hvan : ∀ a v, v ∉ slice d a → F a v = 0) {a : Ix n}
    (hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1) {Kb : ℝ} (hbd : ∀ v, |F a v| ≤ Kb)
    (k : ℕ) (hk : k ≠ 0) : condMom d F 2 a ^ k ≤ condMom d F (2 * k) a := by
  have := isProb_gMeas d hβ
  rw [condMom_eq d hvan hβ two_ne_zero, condMom_eq d hvan hβ (by omega)]
  have mF : Measurable (F a) := hF.comp measurable_prodMk_left
  have h := jensen_pow (gMeas d a) mF hbd k
  simp only [sq_abs] at h ⊢
  exact h

/-- **The integrated cubic price**: `∫_K (K̂³/λ² + Ŷ/((1 − ε₀)²(1 − λ)²)) ≤ cubP`. -/
theorem int_cub_le (D : Design n) (c : Ret n) (d : SplitData n)
    {ε₀ δ₀ L slow : ℝ} (hε0 : 0 ≤ ε₀) (hε₀ : ε₀ < 1) (hL : 0 ≤ L)
    (hslow : 0 < slow)
    (hwin : ∀ a ∈ keptIx D c d, slow ≤ d.S0 a ∧ ∀ v ∈ slice d a,
      |sA D c a v / d.S0 a - 1| ≤ ε₀ ∧ |lA D c a v - d.lam0 a| ≤ δ₀ ∧
      normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2 ≤ L ^ 2)
    {A Dm e6 d6 : ℝ} (hA : 0 ≤ A) (hDm : 0 ≤ Dm) (he6 : 0 ≤ e6) (hd6 : 0 ≤ d6)
    (IA : ∫ a in keptIx D c d, condMom d (epsF D c d) 2 a ^ 2 ∂muI n ≤ A ^ 2)
    (ID : ∫ a in keptIx D c d, condMom d (delF D c d) 2 a ^ 2 ∂muI n ≤ Dm ^ 2)
    (Ie6 : ∫ a in keptIx D c d, condMom d (epsF D c d) 12 a ∂muI n ≤ e6 ^ 12)
    (Id6 : ∫ a in keptIx D c d, condMom d (delF D c d) 12 a ∂muI n ≤ d6 ^ 12)
    {lam lam' : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hl0' : 0 < lam') (hl1' : lam' < 1) :
    IntegrableOn (fun a => (n * ((1 + 3 * ε₀) / (4 * (1 - ε₀))) * condMom d (epsF D c d) 2 a +
          condMom d (delF D c d) 2 a / (2 * (1 - ε₀))) ^ 3 / lam ^ 2 +
        (n * condMom d (epsF D c d) 2 a ^ 2 +
          2 * condMom d (epsF D c d) 2 a * condMom d (delF D c d) 2 a) /
          ((1 - ε₀) ^ 2 * (1 - lam) ^ 2)) (keptIx D c d) (muI n) ∧
    ∫ a in keptIx D c d, ((n * ((1 + 3 * ε₀) / (4 * (1 - ε₀))) * condMom d (epsF D c d) 2 a +
          condMom d (delF D c d) 2 a / (2 * (1 - ε₀))) ^ 3 / lam ^ 2 +
        (n * condMom d (epsF D c d) 2 a ^ 2 +
          2 * condMom d (epsF D c d) 2 a * condMom d (delF D c d) 2 a) /
          ((1 - ε₀) ^ 2 * (1 - lam) ^ 2)) ∂muI n ≤ cubP n ε₀ lam lam' A Dm e6 d6 := by
  set ν := stdGauss (Fin (n - 1))
  set K := keptIx D c d with hKd
  have mK : MeasurableSet K :=
    measurableSet_keptSet ν d.mgood (measurableSet_bulkIx D c) d.eta
  have hKβ : ∀ a ∈ K, removed ν d.good a < 1 := fun a ha => lt_of_le_of_lt ha.2 d.eta_lt
  have hvE : ∀ a v, v ∉ slice d a → epsF D c d a v = 0 := fun a v hv => by
    simp only [epsF, eG, Set.indicator_of_notMem hv]
  have hvD : ∀ a v, v ∉ slice d a → delF D c d a v = 0 := fun a v hv => by
    simp only [delF, dG, Set.indicator_of_notMem hv, mul_zero]
  have mE := measurable_epsF D c d
  have mD := measurable_delF D c d
  have hbE : ∀ a ∈ K, ∀ v, |epsF D c d a v| ≤ ε₀ := fun a ha v => by
    by_cases hv : v ∈ slice d a
    · simp only [epsF, eG, Set.indicator_of_mem hv]; exact ((hwin a ha).2 v hv).1
    · rw [hvE a v hv, abs_zero]; exact hε0
  have hbD : ∀ a ∈ K, ∀ v, |delF D c d a v| ≤ L := fun a ha v => by
    by_cases hv : v ∈ slice d a
    · simp only [delF, dG, Set.indicator_of_mem hv]
      have h := ((hwin a ha).2 v hv).2.2
      have hS : 0 < d.S0 a := lt_of_lt_of_le hslow (hwin a ha).1
      have h2 : √(normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2) ≤ √(L ^ 2) :=
        Real.sqrt_le_sqrt h
      rwa [Real.sqrt_mul (div_nonneg (normSq_nonneg _) hS.le), Real.sqrt_sq_eq_abs,
        Real.sqrt_sq hL, ← abs_of_nonneg (Real.sqrt_nonneg (normSq c.2.1.2 / d.S0 a)),
        ← abs_mul] at h2
    · rw [hvD a v hv, abs_zero]; exact hL
  set X := condMom d (epsF D c d) 2 with hX
  set Y := condMom d (delF D c d) 2 with hY
  set Xi := K.indicator X with hXi
  set Yi := K.indicator Y with hYi
  have mX : Measurable X := measurable_condMom d mE 2
  have mY : Measurable Y := measurable_condMom d mD 2
  have mXi : Measurable Xi := mX.indicator mK
  have mYi : Measurable Yi := mY.indicator mK
  have bX : ∀ a, 0 ≤ Xi a ∧ Xi a ≤ ε₀ ^ 2 := fun a => by
    by_cases ha : a ∈ K
    · simp only [hXi, Set.indicator_of_mem ha]
      exact condMom_bounds d mE hvE (hKβ a ha) (hbE a ha) two_ne_zero
    · simp only [hXi, Set.indicator_of_notMem ha]; exact ⟨le_rfl, sq_nonneg _⟩
  have bY : ∀ a, 0 ≤ Yi a ∧ Yi a ≤ L ^ 2 := fun a => by
    by_cases ha : a ∈ K
    · simp only [hYi, Set.indicator_of_mem ha]
      exact condMom_bounds d mD hvD (hKβ a ha) (hbD a ha) two_ne_zero
    · simp only [hYi, Set.indicator_of_notMem ha]; exact ⟨le_rfl, sq_nonneg _⟩
  have hd : 0 < 1 - ε₀ := by linarith
  set κK := n * ((1 + 3 * ε₀) / (4 * (1 - ε₀))) with hκK
  set βY := 1 / (2 * (1 - ε₀)) with hβY
  have hκK0 : 0 ≤ κK := by positivity
  have hβY0 : 0 ≤ βY := by positivity
  set cc := (1 - ε₀) ^ 2 * (1 - lam) ^ 2 with hcc
  have hcc0 : 0 < cc := mul_pos (pow_pos hd 2) (pow_pos (by linarith) 2)
  set g : ℝ → ℝ → ℝ := fun x y => (κK * x + y / (2 * (1 - ε₀))) ^ 3 / lam ^ 2 +
    (n * x ^ 2 + 2 * x * y) / cc with hg
  have hg0 : g 0 0 = 0 := by simp [hg]
  have hind : K.indicator (fun a => g (X a) (Y a)) = fun a => g (Xi a) (Yi a) := by
    funext a
    by_cases ha : a ∈ K
    · simp only [hXi, hYi, Set.indicator_of_mem ha]
    · simp only [hXi, hYi, Set.indicator_of_notMem ha, hg0]
  have mg : Measurable (fun a => g (Xi a) (Yi a)) := by
    simp only [hg]; fun_prop
  have bpow : ∀ {f : Ix n → ℝ} {M : ℝ}, Measurable f → (∀ a, 0 ≤ f a ∧ f a ≤ M) → ∀ k : ℕ,
      Integrable (fun a => f a ^ k) (muI n) := fun {f} {M} hf hb k =>
    Integrable.of_bound (hf.pow_const k).aestronglyMeasurable (M ^ k)
      (Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hb a).1 k)]
        exact pow_le_pow_left₀ (hb a).1 (hb a).2 k)
  have iXY : Integrable (fun a => Xi a * Yi a) (muI n) :=
    Integrable.of_bound (mXi.mul mYi).aestronglyMeasurable (ε₀ ^ 2 * L ^ 2)
      (Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (bX a).1 (bY a).1)]
        exact mul_le_mul (bX a).2 (bY a).2 (bY a).1 (sq_nonneg _))
  have ig : Integrable (fun a => g (Xi a) (Yi a)) (muI n) := by
    refine Integrable.of_bound mg.aestronglyMeasurable (g (ε₀ ^ 2) (L ^ 2))
      (Filter.Eventually.of_forall fun a => ?_)
    have h0 : 0 ≤ g (Xi a) (Yi a) := by
      simp only [hg]; have := (bX a).1; have := (bY a).1; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    simp only [hg]
    have := (bX a).1; have := (bY a).1; have := (bX a).2; have := (bY a).2
    gcongr
  have iK : IntegrableOn (fun a => g (X a) (Y a)) K (muI n) := by
    rw [← integrable_indicator_iff mK, hind]; exact ig
  refine ⟨iK, ?_⟩
  change ∫ a in K, g (X a) (Y a) ∂muI n ≤ _
  rw [← integral_indicator mK, hind]
  -- the moments of `Xi`, `Yi`
  have conv2 : ∀ {Z : Ix n → ℝ}, ∫ a, (K.indicator Z a) ^ 2 ∂muI n = ∫ a in K, Z a ^ 2 ∂muI n :=
    fun {Z} => by
      rw [← integral_indicator mK]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      by_cases ha : a ∈ K
      · simp only [Set.indicator_of_mem ha]
      · simp only [Set.indicator_of_notMem ha]; norm_num
  have IX2 : ∫ a, Xi a ^ 2 ∂muI n ≤ A ^ 2 := by rw [hXi, conv2]; exact IA
  have IY2 : ∫ a, Yi a ^ 2 ∂muI n ≤ Dm ^ 2 := by rw [hYi, conv2]; exact ID
  have six : ∀ {F : Ix n → (Fin (n - 1) → ℝ) → ℝ} {Kb : ℝ}, Measurable (Function.uncurry F) →
      (∀ a v, v ∉ slice d a → F a v = 0) → (∀ a ∈ K, ∀ v, |F a v| ≤ Kb) → ∀ {e : ℝ},
      ∫ a in K, condMom d F 12 a ∂muI n ≤ e ^ 12 →
      ∫ a, (K.indicator (condMom d F 2) a) ^ 6 ∂muI n ≤ e ^ 12 := by
    intro F Kb hF hvan hbd e hI
    refine le_trans ?_ hI
    rw [← integral_indicator mK]
    have mC12 : Measurable (condMom d F 12) := measurable_condMom d hF 12
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => ?_) ?_
      (Filter.Eventually.of_forall fun a => ?_)
    · by_cases ha : a ∈ K
      · simp only [Set.indicator_of_mem ha]
        exact pow_nonneg (condMom_bounds d hF hvan (hKβ a ha) (hbd a ha) two_ne_zero).1 6
      · simp only [Set.indicator_of_notMem ha]; norm_num
    · rw [integrable_indicator_iff mK]
      refine Integrable.of_bound mC12.aestronglyMeasurable (|Kb| ^ 12)
        (ae_restrict_of_forall_mem mK fun a ha => ?_)
      have hb' : ∀ v, |F a v| ≤ |Kb| := fun v => (hbd a ha v).trans (le_abs_self _)
      obtain ⟨b0, b1⟩ := condMom_bounds d hF hvan (hKβ a ha) hb' (show 12 ≠ 0 by norm_num)
      rw [Real.norm_eq_abs, abs_of_nonneg b0]; exact b1
    · by_cases ha : a ∈ K
      · simp only [Set.indicator_of_mem ha]
        exact condMom2_pow_le d hF hvan (hKβ a ha) (hbd a ha) 6 (by norm_num)
      · simp only [Set.indicator_of_notMem ha]; norm_num
  have IX6 : ∫ a, Xi a ^ 6 ∂muI n ≤ e6 ^ 12 := six mE hvE hbE Ie6
  have IY6 : ∫ a, Yi a ^ 6 ∂muI n ≤ d6 ^ 12 := six mD hvD hbD Id6
  have IX3 := int_cube_le (muI n) mXi bX hA he6 IX2 IX6
  have IY3 := int_cube_le (muI n) mYi bY hDm hd6 IY2 IY6
  have IXY : ∫ a, Xi a * Yi a ∂muI n ≤ A * Dm := by
    have h := BstLean.Part138.cs_sq (muI n) (bpow mXi bX 2) (bpow mYi bY 2) iXY
    have h0 : 0 ≤ ∫ a, Xi a * Yi a ∂muI n :=
      integral_nonneg fun a => mul_nonneg (bX a).1 (bY a).1
    have h2 : (∫ a, Xi a * Yi a ∂muI n) ^ 2 ≤ (A * Dm) ^ 2 := by
      rw [mul_pow]
      exact h.trans (mul_le_mul IX2 IY2 (integral_nonneg fun a => sq_nonneg _) (sq_nonneg _))
    exact (pow_le_pow_iff_left₀ h0 (mul_nonneg hA hDm) two_ne_zero).mp h2
  -- the pointwise convexity split and the integral
  have hpt : ∀ a, g (Xi a) (Yi a) ≤ (κK ^ 3 / lam' ^ 2 / lam ^ 2) * Xi a ^ 3 +
      (βY ^ 3 / (1 - lam') ^ 2 / lam ^ 2) * Yi a ^ 3 + n / cc * Xi a ^ 2 +
      2 / cc * (Xi a * Yi a) := fun a => by
    simp only [hg]
    have h1 := cube_split (mul_nonneg hκK0 (bX a).1) (mul_nonneg hβY0 (bY a).1) hl0' hl1'
    have e : Yi a / (2 * (1 - ε₀)) = βY * Yi a := by simp only [hβY]; ring
    rw [e]
    have hl2 : 0 < lam ^ 2 := by positivity
    have h2 := div_le_div_of_nonneg_right h1 hl2.le
    have e2 : ((κK * Xi a) ^ 3 / lam' ^ 2 + (βY * Yi a) ^ 3 / (1 - lam') ^ 2) / lam ^ 2 =
        (κK ^ 3 / lam' ^ 2 / lam ^ 2) * Xi a ^ 3 + (βY ^ 3 / (1 - lam') ^ 2 / lam ^ 2) * Yi a ^ 3 := by
      ring
    have e3 : (n * Xi a ^ 2 + 2 * Xi a * Yi a) / cc = n / cc * Xi a ^ 2 + 2 / cc * (Xi a * Yi a) := by
      ring
    rw [e3]
    linarith
  have iR : Integrable (fun a => (κK ^ 3 / lam' ^ 2 / lam ^ 2) * Xi a ^ 3 +
      (βY ^ 3 / (1 - lam') ^ 2 / lam ^ 2) * Yi a ^ 3 + n / cc * Xi a ^ 2 +
      2 / cc * (Xi a * Yi a)) (muI n) :=
    ((((bpow mXi bX 3).const_mul _).add ((bpow mYi bY 3).const_mul _)).add
      ((bpow mXi bX 2).const_mul _)).add (iXY.const_mul _)
  refine (integral_mono ig iR hpt).trans ?_
  set k1c := κK ^ 3 / lam' ^ 2 / lam ^ 2 with hk1c
  set k2c := βY ^ 3 / (1 - lam') ^ 2 / lam ^ 2 with hk2c
  have j1 : Integrable (fun a => k1c * Xi a ^ 3) (muI n) := (bpow mXi bX 3).const_mul _
  have j2 : Integrable (fun a => k2c * Yi a ^ 3) (muI n) := (bpow mYi bY 3).const_mul _
  have j3 : Integrable (fun a => (n : ℝ) / cc * Xi a ^ 2) (muI n) := (bpow mXi bX 2).const_mul _
  have j4 : Integrable (fun a => 2 / cc * (Xi a * Yi a)) (muI n) := iXY.const_mul _
  rw [integral_add (f := fun a => k1c * Xi a ^ 3 + k2c * Yi a ^ 3 + (n : ℝ) / cc * Xi a ^ 2)
      (g := fun a => 2 / cc * (Xi a * Yi a)) ((j1.add j2).add j3) j4,
    integral_add (f := fun a => k1c * Xi a ^ 3 + k2c * Yi a ^ 3)
      (g := fun a => (n : ℝ) / cc * Xi a ^ 2) (j1.add j2) j3,
    integral_add (f := fun a => k1c * Xi a ^ 3) (g := fun a => k2c * Yi a ^ 3) j1 j2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  unfold cubP
  have hl2 : 0 < lam ^ 2 := by positivity
  have hl2' : 0 < lam' ^ 2 := by positivity
  have hm2' : 0 < (1 - lam') ^ 2 := pow_pos (by linarith) 2
  have k1 : 0 ≤ k1c := by positivity
  have k2 : 0 ≤ k2c := by positivity
  have k3 : 0 ≤ (n : ℝ) / cc := by positivity
  have k4 : 0 ≤ (2 : ℝ) / cc := by positivity
  have t1 := mul_le_mul_of_nonneg_left IX3 k1
  have t2 := mul_le_mul_of_nonneg_left IY3 k2
  have t3 := mul_le_mul_of_nonneg_left IX2 k3
  have t4 := mul_le_mul_of_nonneg_left IXY k4
  have efin : ((κK ^ 3 * (A * √A * e6 ^ 3) / lam' ^ 2 +
      (1 / (2 * (1 - ε₀))) ^ 3 * (Dm * √Dm * d6 ^ 3) / (1 - lam') ^ 2) / lam ^ 2 +
      (n * A ^ 2 + 2 * A * Dm) / cc) =
      κK ^ 3 / lam' ^ 2 / lam ^ 2 * (A * √A * e6 ^ 3) +
        βY ^ 3 / (1 - lam') ^ 2 / lam ^ 2 * (Dm * √Dm * d6 ^ 3) + n / cc * A ^ 2 +
        2 / cc * (A * Dm) := by
    simp only [hβY]; ring
  rw [show (n : ℝ) * ((1 + 3 * ε₀) / (4 * (1 - ε₀))) = κK from rfl, ← hcc, efin]
  linarith


/-- **Part 162's `fluct_of_moments` with Lemma HQ**: the conclusion is `FLUCT_hyp` with the
middle root `√(𝒞/4 + (3/4)·cubP)`. -/
theorem fluct_of_moments_hq (D : Design n) (t : ℝ) (c : Ret n) (d : SplitData n)
    {ε₀ δ₀ L slow : ℝ} (hε0 : 0 ≤ ε₀) (hε₀ : ε₀ < 1) (hδ0 : 0 ≤ δ₀) (hL : 0 ≤ L)
    (hslow : 0 < slow) (hcA : 0 < normSq c.2.1.2)
    (hwin : ∀ a ∈ keptIx D c d, slow ≤ d.S0 a ∧ ∀ v ∈ slice d a,
      |sA D c a v / d.S0 a - 1| ≤ ε₀ ∧ |lA D c a v - d.lam0 a| ≤ δ₀ ∧
      normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2 ≤ L ^ 2)
    (hcent : ∀ a ∈ keptIx D c d,
      ∫ v in slice d a, (lA D c a v - d.lam0 a) ∂stdGauss (Fin (n - 1)) = 0 ∧
      ∫ v in slice d a, (sA D c a v / d.S0 a - 1) ∂stdGauss (Fin (n - 1)) = 0)
    {B Dd A Dm e4 d4 e6 d6 hfl : ℝ} (hA : 0 ≤ A) (hDm : 0 ≤ Dm) (he4 : 0 ≤ e4) (hd4 : 0 ≤ d4)
    (he6 : 0 ≤ e6) (hd6 : 0 ≤ d6)
    (hB : ∫ a, removed (stdGauss (Fin (n - 1))) d.good a ∂muI n ≤ B)
    (hD : ∫ a in keptIx D c d, hellG2 n ((d.lam0 a - d.lamb a) ^ 2 * normSq c.2.1.2) (d.S0 a)
      (d.Sb a) ∂muI n ≤ Dd)
    (IA : ∫ a in keptIx D c d, condMom d (epsF D c d) 2 a ^ 2 ∂muI n ≤ A ^ 2)
    (ID : ∫ a in keptIx D c d, condMom d (delF D c d) 2 a ^ 2 ∂muI n ≤ Dm ^ 2)
    (Ie4 : ∫ a in keptIx D c d, condMom d (epsF D c d) 8 a ∂muI n ≤ e4 ^ 8)
    (Id4 : ∫ a in keptIx D c d, condMom d (delF D c d) 8 a ∂muI n ≤ d4 ^ 8)
    (Ie6 : ∫ a in keptIx D c d, condMom d (epsF D c d) 12 a ∂muI n ≤ e6 ^ 12)
    (Id6 : ∫ a in keptIx D c d, condMom d (delF D c d) 12 a ∂muI n ≤ d6 ^ 12)
    {lam lam' : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hl0' : 0 < lam') (hl1' : lam' < 1)
    (hsum : √(2 * (1 + d.eta⁻¹) * B) + √(priceC (1 - ε₀ ^ 2)⁻¹ n L ε₀
        (exp ((1 - ε₀ ^ 2)⁻¹ * (n * ε₀ ^ 2 / 2 + L ^ 2 * (1 + ε₀)))) A Dm e4 d4 e6 d6 / 4 +
        3 / 4 * cubP n ε₀ lam lam' A Dm e6 d6) + √Dd ≤ hfl) :
    FLUCT_hyp D t c d hfl := by
  set ν := stdGauss (Fin (n - 1))
  set K := keptIx D c d with hKd
  have mK : MeasurableSet K :=
    measurableSet_keptSet ν d.mgood (measurableSet_bulkIx D c) d.eta
  have hKβ : ∀ a ∈ K, removed ν d.good a < 1 := fun a ha => lt_of_le_of_lt ha.2 d.eta_lt
  refine ⟨B, priceC (1 - ε₀ ^ 2)⁻¹ n L ε₀
        (exp ((1 - ε₀ ^ 2)⁻¹ * (n * ε₀ ^ 2 / 2 + L ^ 2 * (1 + ε₀)))) A Dm e4 d4 e6 d6 / 4 +
        3 / 4 * cubP n ε₀ lam lam' A Dm e6 d6, Dd, hB, ?_, hD, hsum⟩
  have hchi := int_chiK_le D c d hε0 hε₀ hδ0 hL hslow hcA hwin hcent hA hDm he4 hd4 he6 hd6
    IA ID Ie4 Id4 Ie6 Id6
  obtain ⟨icub, hcub⟩ := int_cub_le D c d hε0 hε₀ hL hslow hwin hA hDm he6 hd6 IA ID Ie6 Id6
    hl0 hl1 hl0' hl1'
  have mpl := measurable_pLat D t c
  have hpl0 : ∀ q, 0 ≤ pLat D t c q := fun q => gP_nonneg _ _ _
  have hpl1 : ∀ q, pLat D t c q ≤ 1 := fun q => gP_le_one _ _ _
  have mq0 : Measurable (q0Lat t c d) :=
    measurable_gP_comp (measurableSet_clsSet c t) (d.mlam0.smul_const _) d.mS0
  have mX : Measurable (fun a => (√(goodMean ν d.good (pLat D t c) a) - √(q0Lat t c d a)) ^ 2) :=
    (((measurable_goodMean ν d.mgood mpl).sqrt).sub mq0.sqrt).pow_const 2
  have iX : IntegrableOn (fun a => (√(goodMean ν d.good (pLat D t c) a) - √(q0Lat t c d a)) ^ 2)
      K (muI n) := by
    refine Integrable.of_bound mX.aestronglyMeasurable 1 (ae_restrict_of_forall_mem mK fun a ha => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨h0, h1, _⟩ := goodMean_bounds ν d.mgood mpl hpl0 hpl1 a (hKβ a ha)
    exact sqrt_sub_sq_le_one h0 h1 (gP_nonneg _ _ _) (gP_le_one _ _ _)
  have iC : IntegrableOn (chiK D c d) K (muI n) := by
    set Mc := (√(1 - ε₀ ^ 2))⁻¹ ^ n *
      exp ((1 + ε₀) * (normSq c.2.1.2 / slow) * δ₀ ^ 2 / (1 - ε₀ ^ 2))
    refine Integrable.of_bound (measurable_chiK D c d).aestronglyMeasurable (Mc + 1)
      (ae_restrict_of_forall_mem mK fun a ha => ?_)
    obtain ⟨b1, b2⟩ := chiK_bounds D c d hε0 hε₀ hslow a (hKβ a ha) (hwin a ha).1
      (fun v hv => ⟨((hwin a ha).2 v hv).1, ((hwin a ha).2 v hv).2.1⟩)
    have hM0 : 0 ≤ Mc :=
      mul_nonneg (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _) (exp_pos _).le
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hpt : ∀ a ∈ K, (√(goodMean ν d.good (pLat D t c) a) - √(q0Lat t c d a)) ^ 2 ≤
      chiK D c d a / 4 + 3 / 4 *
        ((n * ((1 + 3 * ε₀) / (4 * (1 - ε₀))) * condMom d (epsF D c d) 2 a +
          condMom d (delF D c d) 2 a / (2 * (1 - ε₀))) ^ 3 / lam ^ 2 +
        (n * condMom d (epsF D c d) 2 a ^ 2 +
          2 * condMom d (epsF D c d) 2 a * condMom d (delF D c d) 2 a) /
          ((1 - ε₀) ^ 2 * (1 - lam) ^ 2)) := fun a ha =>
    root_le_hq D t c d a (hKβ a ha) (lt_of_lt_of_le hslow (hwin a ha).1) hε0 hε₀ hδ0
      (fun v hv => ⟨((hwin a ha).2 v hv).1, ((hwin a ha).2 v hv).2.1⟩) (hcent a ha).1
      (hcent a ha).2 hl0 hl1
  refine (setIntegral_mono_on iX ((iC.div_const 4).add (icub.const_mul (3 / 4))) mK hpt).trans
    (le_of_eq_of_le (integral_add (iC.div_const 4) (icub.const_mul (3 / 4))) ?_)
  rw [integral_div, integral_const_mul]
  linarith

/-- **Part 162's `fluct_paper` with Lemma HQ** (conclusion `FLUCT_hyp`). -/
theorem fluct_paper_hq (hn : 1 ≤ n) (D : Design n) (c : Ret n) (t : ℝ) {wl ws σl η : ℝ} (hwl : 0 ≤ wl)
    (hws : 0 < ws) (hσl : 0 < σl) (h0 : 0 < η) (h1 : η < 1) (hcA : 0 < normSq c.2.1.2)
    {CA : ℝ} (hCA : normSq c.2.1.2 ≤ CA) (hε : eps0 ws σl < 1)
    {Vs Vl ts8 ts12 tl8 tl12 B Dd hfl : ℝ} (hVs0 : 0 ≤ Vs) (hVl0 : 0 ≤ Vl) (hts8 : 0 < ts8)
    (hts12 : 0 < ts12) (htl8 : 0 < tl8) (htl12 : 0 < tl12)
    (hVs : ∫ a, (∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ Vs ^ 2)
    (hVl : ∫ a, (∫ v, (lA D c a v - lbar D c a) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ Vl ^ 2)
    (hs8 : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ ts8 ^ 8)
    (hs12 : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ ts12 ^ 12)
    (hl8 : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tl8 ^ 8)
    (hl12 : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tl12 ^ 12)
    (hB : ∫ a, removed (stdGauss (Fin (n - 1))) (goodP D c wl ws σl) a ∂muI n ≤ B)
    (hD : ∫ a in keptIx D c (dPaper D c wl ws σl η h0 h1), hellG2 n
      (((dPaper D c wl ws σl η h0 h1).lam0 a - (dPaper D c wl ws σl η h0 h1).lamb a) ^ 2 *
        normSq c.2.1.2) ((dPaper D c wl ws σl η h0 h1).S0 a) ((dPaper D c wl ws σl η h0 h1).Sb a)
        ∂muI n ≤ Dd)
    {lam lam' : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hl0' : 0 < lam') (hl1' : lam' < 1)
    (hsum : √(2 * (1 + η⁻¹) * B) + √(priceC (1 - eps0 ws σl ^ 2)⁻¹ n (√CA * (2 * wl) / σl)
        (eps0 ws σl) (exp ((1 - eps0 ws σl ^ 2)⁻¹ * (n * eps0 ws σl ^ 2 / 2 +
          (√CA * (2 * wl) / σl) ^ 2 * (1 + eps0 ws σl))))
        (cVw ws σl * ((1 - η)⁻¹ * Vs)) (CA / σl ^ 2 * ((1 - η)⁻¹ * Vl))
        (cEw ws σl * ((iotaP η 8 + c2η η + c3η η ws σl) * ts8))
        (√CA / σl * ((iotaP η 8 + c2η η) * tl8))
        (cEw ws σl * ((iotaP η 12 + c2η η + c3η η ws σl) * ts12))
        (√CA / σl * ((iotaP η 12 + c2η η) * tl12)) / 4 +
        3 / 4 * cubP n (eps0 ws σl) lam lam' (cVw ws σl * ((1 - η)⁻¹ * Vs))
          (CA / σl ^ 2 * ((1 - η)⁻¹ * Vl))
          (cEw ws σl * ((iotaP η 12 + c2η η + c3η η ws σl) * ts12))
          (√CA / σl * ((iotaP η 12 + c2η η) * tl12))) + √Dd ≤ hfl) :
    FLUCT_hyp D t c (dPaper D c wl ws σl η h0 h1) hfl := by
  set ν := stdGauss (Fin (n - 1)) with hν
  set d := dPaper D c wl ws σl η h0 h1 with hd
  set K := keptIx D c d with hK
  have mK : MeasurableSet K := measurableSet_keptSet ν d.mgood (measurableSet_bulkIx D c) d.eta
  have hCA0 : 0 ≤ CA := (normSq_nonneg _).trans hCA
  set L := √CA * (2 * wl) / σl with hL
  have hL0 : 0 ≤ L := by positivity
  have hε0 : 0 ≤ eps0 ws σl := by
    unfold eps0; have : 0 ≤ 2 * ws / σl := by positivity
    nlinarith
  have mS : ∀ a, Measurable (fun v => sgA D c a v) := fun a => measurable_sgA_left D c a
  have mLa : ∀ a, Measurable (fun v => lA D c a v) := fun a => measurable_lA_left D c a
  have bS : ∀ a v, |sgA D c a v| ≤ lipSig D c := abs_sgA_le hn D c
  have bLa : ∀ a v, |lA D c a v| ≤ lipLam D c := abs_lA_le hn D c
  -- window
  have hwin : ∀ a ∈ K, σl ^ 2 ≤ d.S0 a ∧ ∀ v ∈ slice d a,
      |sA D c a v / d.S0 a - 1| ≤ eps0 ws σl ∧ |lA D c a v - d.lam0 a| ≤ 2 * wl ∧
      normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2 ≤ L ^ 2 := by
    intro a ha
    obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
    obtain ⟨lo, hi, hlo, hhi, hG', s1, s2, -, -⟩ :=
      idx_scale (measurableSet_slice d a) hm (mS a) (bS a) hws.le hσl hGψ
    have hS0 : σl ^ 2 ≤ d.S0 a := by rw [hS]; exact (pow_le_pow_left₀ hσl.le hlo 2).trans s1
    have hφw := idx_phi_window (measurableSet_slice d a) hm (mLa a) (bLa a) hGφ
    refine ⟨hS0, fun v hv => ⟨?_, ?_, ?_⟩⟩
    · rw [sA_eq, hS]
      obtain ⟨x1, x2⟩ := hG' v hv
      exact idx_eps_window hσl hws.le hlo hhi s1 s2 x1 x2
    · rw [hl]; exact hφw v hv
    · have hδ := hφw v hv
      rw [← hl] at hδ
      have h2 : (lA D c a v - d.lam0 a) ^ 2 ≤ (2 * wl) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
      have h3 : normSq c.2.1.2 / d.S0 a ≤ CA / σl ^ 2 :=
        div_le_div₀ hCA0 hCA (by positivity) hS0
      calc normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2 ≤ CA / σl ^ 2 * (2 * wl) ^ 2 :=
            mul_le_mul h3 h2 (sq_nonneg _) (by positivity)
        _ = L ^ 2 := by rw [hL, div_pow, mul_pow (√CA), Real.sq_sqrt hCA0]; ring
  -- centring
  have hcent : ∀ a ∈ K, ∫ v in slice d a, (lA D c a v - d.lam0 a) ∂ν = 0 ∧
      ∫ v in slice d a, (sA D c a v / d.S0 a - 1) ∂ν = 0 := by
    intro a ha
    obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
    have ms := measurableSet_slice d a
    have key : ∀ f : (Fin (n - 1) → ℝ) → ℝ, ∫ v in slice d a, f v ∂ν =
        ν.real (slice d a) * ∫ v, f v ∂nrm ν (slice d a) := fun f => by
      rw [integral_nrm ν ms hm, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul, integral_indicator ms]
    obtain ⟨lo, hi, hlo, hhi, hG', s1, s2, -, -⟩ := idx_scale ms hm (mS a) (bS a) hws.le hσl hGψ
    have hS0p : 0 < d.S0 a := by
      rw [hS]; exact lt_of_lt_of_le (by have := lt_of_lt_of_le hσl hlo; positivity) s1
    have iL : IntegrableOn (fun v => lA D c a v) (slice d a) ν := (intB (mLa a) (bLa a)).integrableOn
    have iSA : IntegrableOn (fun v => sA D c a v / d.S0 a) (slice d a) ν :=
      (intB (((mS a).pow_const 2).div_const _) (M := lipSig D c ^ 2 / d.S0 a) fun v => by
        rw [abs_div, abs_of_pos hS0p]
        exact div_le_div_of_nonneg_right (sq_bound_of_abs (bS a) v) hS0p.le).integrableOn
    constructor
    · rw [integral_sub iL (integrableOn_const (by simp)), setIntegral_const, key, hl]
      simp only [smul_eq_mul]; ring
    · rw [integral_sub iSA (integrableOn_const (by simp)), setIntegral_const, key, integral_div]
      simp only [sA_eq, smul_eq_mul]
      rw [← hS]; field_simp; ring
  -- the fields as functions of `(a, v)` and their bounds
  have hvE : ∀ a v, v ∉ slice d a → epsF D c d a v = 0 := fun a v hv => by
    simp only [epsF, eG, Set.indicator_of_notMem hv]
  have hvD : ∀ a v, v ∉ slice d a → delF D c d a v = 0 := fun a v hv => by
    simp only [delF, dG, Set.indicator_of_notMem hv, mul_zero]
  have mE := measurable_epsF D c d
  have mD := measurable_delF D c d
  have hKβ : ∀ a ∈ K, removed ν d.good a < 1 := fun a ha => lt_of_le_of_lt ha.2 d.eta_lt
  have hbE : ∀ a ∈ K, ∀ v, |epsF D c d a v| ≤ eps0 ws σl := fun a ha v => by
    by_cases hv : v ∈ slice d a
    · simp only [epsF, eG, Set.indicator_of_mem hv]; exact ((hwin a ha).2 v hv).1
    · rw [hvE a v hv, abs_zero]; exact hε0
  have hbD : ∀ a ∈ K, ∀ v, |delF D c d a v| ≤ L := fun a ha v => by
    by_cases hv : v ∈ slice d a
    · simp only [delF, dG, Set.indicator_of_mem hv]
      have h := ((hwin a ha).2 v hv).2.2
      have hS : 0 < d.S0 a := lt_of_lt_of_le (by positivity) (hwin a ha).1
      have h2 : √(normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2) ≤ √(L ^ 2) :=
        Real.sqrt_le_sqrt h
      rwa [Real.sqrt_mul (div_nonneg (normSq_nonneg _) hS.le), Real.sqrt_sq_eq_abs,
        Real.sqrt_sq hL0, ← abs_of_nonneg (Real.sqrt_nonneg (normSq c.2.1.2 / d.S0 a)),
        ← abs_mul] at h2
    · rw [hvD a v hv, abs_zero]; exact hL0
  -- the latitude moments as functions of `a`
  have hgb : ∀ a, |gbar D c a| ≤ lipSig D c := fun a => by
    unfold gbar
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |sgA D c a v| ∂ν ≤ ∫ _v, lipSig D c ∂ν :=
          integral_mono (intB (mS a).abs (M := lipSig D c) fun v => by rw [abs_abs]; exact bS a v)
            (integrable_const _) (bS a)
      _ = lipSig D c := by simp
  have hlb : ∀ a, |lbar D c a| ≤ lipLam D c := fun a => by
    unfold lbar
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |lA D c a v| ∂ν ≤ ∫ _v, lipLam D c ∂ν :=
          integral_mono (intB (mLa a).abs (M := lipLam D c) fun v => by rw [abs_abs]; exact bLa a v)
            (integrable_const _) (bLa a)
      _ = lipLam D c := by simp
  set Ks := 2 * lipSig D c with hKs
  set Kl := 2 * lipLam D c with hKl
  have hKs0 : 0 ≤ Ks := by have := lipSig_nonneg D c; positivity
  have hKl0 : 0 ≤ Kl := by have := lipLam_nonneg D c; positivity
  have bYs : ∀ a v, |sgA D c a v - gbar D c a| ≤ Ks := fun a v =>
    (abs_sub _ _).trans (by linarith [bS a v, hgb a])
  have bYl : ∀ a v, |lA D c a v - lbar D c a| ≤ Kl := fun a v =>
    (abs_sub _ _).trans (by linarith [bLa a v, hlb a])
  have mYs : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => sgA D c p.1 p.2 - gbar D c p.1) :=
    (measurable_sgA D c).sub ((measurable_gbar D c).comp measurable_fst)
  have mYl : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => lA D c p.1 p.2 - lbar D c p.1) :=
    (measurable_lA D c).sub ((measurable_lbar D c).comp measurable_fst)
  have mInt : ∀ {F : Ix n × (Fin (n - 1) → ℝ) → ℝ}, Measurable F →
      Measurable (fun a => ∫ v, F (a, v) ∂ν) := fun hF =>
    (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have mVs : Measurable (fun a => ∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν) := mInt (mYs.pow_const 2)
  have mVl : Measurable (fun a => ∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν) := mInt (mYl.pow_const 2)
  have mMs : ∀ p : ℕ, Measurable (fun a => ∫ v, |sgA D c a v - gbar D c a| ^ p ∂ν) := fun p =>
    mInt (mYs.abs.pow_const p)
  have mMl : ∀ p : ℕ, Measurable (fun a => ∫ v, |lA D c a v - lbar D c a| ^ p ∂ν) := fun p =>
    mInt (mYl.abs.pow_const p)
  have bInt : ∀ {f : (Fin (n - 1) → ℝ) → ℝ} {M : ℝ}, Measurable f → (∀ v, 0 ≤ f v) →
      (∀ v, f v ≤ M) → 0 ≤ ∫ v, f v ∂ν ∧ ∫ v, f v ∂ν ≤ M := fun {f} {M} hf h0 hM => by
    refine ⟨integral_nonneg h0, ?_⟩
    calc ∫ v, f v ∂ν ≤ ∫ _v, M ∂ν :=
          integral_mono (intB hf (M := M) fun v => by rw [abs_of_nonneg (h0 v)]; exact hM v)
            (integrable_const _) hM
      _ = M := by simp
  have bVs : ∀ a, 0 ≤ ∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν ∧
      ∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν ≤ Ks ^ 2 := fun a =>
    bInt (((mS a).sub_const _).pow_const 2) (fun v => sq_nonneg _)
      (fun v => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bYs a v) 2)
  have bVl : ∀ a, 0 ≤ ∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν ∧
      ∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν ≤ Kl ^ 2 := fun a =>
    bInt (((mLa a).sub_const _).pow_const 2) (fun v => sq_nonneg _)
      (fun v => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bYl a v) 2)
  have bMs : ∀ p : ℕ, ∀ a, 0 ≤ ∫ v, |sgA D c a v - gbar D c a| ^ p ∂ν ∧
      ∫ v, |sgA D c a v - gbar D c a| ^ p ∂ν ≤ Ks ^ p := fun p a =>
    bInt (((mS a).sub_const _).abs.pow_const p) (fun v => pow_nonneg (abs_nonneg _) _)
      (fun v => pow_le_pow_left₀ (abs_nonneg _) (bYs a v) p)
  have bMl : ∀ p : ℕ, ∀ a, 0 ≤ ∫ v, |lA D c a v - lbar D c a| ^ p ∂ν ∧
      ∫ v, |lA D c a v - lbar D c a| ^ p ∂ν ≤ Kl ^ p := fun p a =>
    bInt (((mLa a).sub_const _).abs.pow_const p) (fun v => pow_nonneg (abs_nonneg _) _)
      (fun v => pow_le_pow_left₀ (abs_nonneg _) (bYl a v) p)
  have hηm : ∀ a ∈ K, (ν.real (slice d a))⁻¹ ≤ (1 - η)⁻¹ := fun a ha =>
    inv_anti₀ (by linarith) (kept_facts hn D c h0 h1 ha).2.1
  have hc2 : 0 < c2η η := Real.sqrt_pos.mpr (div_pos h0 (by linarith))
  have hc3 : 0 < c3η η ws σl := by
    unfold c3η; have := Real.sqrt_pos.mpr (show (0:ℝ) < 1 - η by linarith); positivity
  have hcE : 0 ≤ cEw ws σl := by unfold cEw; positivity
  have hcV : 0 ≤ cVw ws σl := by unfold cVw; positivity
  -- the square-root of the variance and Jensen
  have msd : ∀ (F : Ix n → (Fin (n - 1) → ℝ) → ℝ),
      Measurable (fun a => ∫ v, F a v ^ 2 ∂ν) → Measurable (fun a => √(∫ v, F a v ^ 2 ∂ν)) :=
    fun F h => h.sqrt
  have sd_pow : ∀ {x : ℝ}, 0 ≤ x → ∀ k : ℕ, √x ^ (2 * k) = x ^ k := fun {x} hx k => by
    rw [pow_mul, Real.sq_sqrt hx]
  -- (IA)
  have IA : ∫ a in K, condMom d (epsF D c d) 2 a ^ 2 ∂muI n ≤ (cVw ws σl * ((1 - η)⁻¹ * Vs)) ^ 2 := by
    set q : Ix n → ℝ := fun a => cVw ws σl * ((1 - η)⁻¹ * ∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν)
      with hq
    have hqa : ∀ a ∈ K, condMom d (epsF D c d) 2 a ^ 2 ≤ q a ^ 2 := by
      intro a ha
      obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
      have h0' := (condMom_bounds d mE hvE (hKβ a ha) (hbE a ha) two_ne_zero).1
      have h2 := idx_eps_sq (measurableSet_slice d a) hm (mS a) (bS a) hws.le hσl hGψ
      have bd : ∀ v, |sgA D c a v - ∫ w, sgA D c a w ∂ν| ≤ Ks := bYs a
      have h3 := integral_nrm_le (measurableSet_slice d a) hm
        (g := fun v => (sgA D c a v - ∫ w, sgA D c a w ∂ν) ^ 2) (fun v => sq_nonneg _)
        (intB (((mS a).sub_const _).pow_const 2) (sq_bound_of_abs bd))
      have hle : condMom d (epsF D c d) 2 a ≤ q a := by
        rw [cm_eps hn D c h0 h1 ha two_ne_zero]
        simp_rw [sq_abs]
        refine h2.trans ?_
        simp only [hq, cVw]
        refine mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_right (hηm a ha)
          (integral_nonneg fun v => sq_nonneg _))) (by positivity)
      exact pow_le_pow_left₀ h0' hle 2
    have iq : Integrable (fun a => q a ^ 2) (muI n) :=
      intB ((mVs.const_mul _ |>.const_mul _).pow_const 2)
        (M := (cVw ws σl * ((1 - η)⁻¹ * Ks ^ 2)) ^ 2) fun a => by
          rw [abs_of_nonneg (sq_nonneg _)]
          have := bVs a
          have hη' : 0 ≤ (1 - η)⁻¹ := inv_nonneg.mpr (by linarith)
          exact pow_le_pow_left₀ (by positivity) (by
            simp only [hq]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this.2 hη') hcV) 2
    have iC : IntegrableOn (fun a => condMom d (epsF D c d) 2 a ^ 2) K (muI n) := by
      refine Integrable.of_bound ((measurable_condMom d mE 2).pow_const 2).aestronglyMeasurable
        ((eps0 ws σl ^ 2) ^ 2) (ae_restrict_of_forall_mem mK fun a ha => ?_)
      obtain ⟨b0, b1⟩ := condMom_bounds d mE hvE (hKβ a ha) (hbE a ha) two_ne_zero
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ b0 b1 2
    calc ∫ a in K, condMom d (epsF D c d) 2 a ^ 2 ∂muI n ≤ ∫ a in K, q a ^ 2 ∂muI n :=
          setIntegral_mono_on iC iq.integrableOn mK hqa
      _ ≤ ∫ a, q a ^ 2 ∂muI n :=
          setIntegral_le_integral iq (Filter.Eventually.of_forall fun a => sq_nonneg _)
      _ = (cVw ws σl * (1 - η)⁻¹) ^ 2 *
            ∫ a, (∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν) ^ 2 ∂muI n := by
          rw [← integral_const_mul]; congr 1; funext a; simp only [hq]; ring
      _ ≤ (cVw ws σl * (1 - η)⁻¹) ^ 2 * Vs ^ 2 := mul_le_mul_of_nonneg_left hVs (sq_nonneg _)
      _ = _ := by ring
  -- (ID)
  have ID : ∫ a in K, condMom d (delF D c d) 2 a ^ 2 ∂muI n ≤
      (CA / σl ^ 2 * ((1 - η)⁻¹ * Vl)) ^ 2 := by
    set q : Ix n → ℝ := fun a => CA / σl ^ 2 * ((1 - η)⁻¹ * ∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν)
      with hq
    have hqa : ∀ a ∈ K, condMom d (delF D c d) 2 a ^ 2 ≤ q a ^ 2 := by
      intro a ha
      obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
      have h0' := (condMom_bounds d mD hvD (hKβ a ha) (hbD a ha) two_ne_zero).1
      have hS0 : σl ^ 2 ≤ ∫ w, sgA D c a w ^ 2 ∂nrm ν (slice d a) := hS ▸ (hwin a ha).1
      have h2 := idx_del_sq (measurableSet_slice d a) hm (mLa a) (bLa a) hσl hS0
        (normSq_nonneg c.2.1.2) hm1 h1
      have hle : condMom d (delF D c d) 2 a ≤ q a := by
        rw [cm_del hn D c h0 h1 ha two_ne_zero]
        simp_rw [sq_abs]
        refine h2.trans ?_
        simp only [hq]
        refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCA (by positivity)) ?_
        have : 0 ≤ (1 - η)⁻¹ := inv_nonneg.mpr (by linarith)
        have := (bVl a).1
        positivity
      exact pow_le_pow_left₀ h0' hle 2
    have iq : Integrable (fun a => q a ^ 2) (muI n) :=
      intB ((mVl.const_mul _ |>.const_mul _).pow_const 2)
        (M := (CA / σl ^ 2 * ((1 - η)⁻¹ * Kl ^ 2)) ^ 2) fun a => by
          rw [abs_of_nonneg (sq_nonneg _)]
          have := bVl a
          have hη' : 0 ≤ (1 - η)⁻¹ := inv_nonneg.mpr (by linarith)
          exact pow_le_pow_left₀ (by positivity) (by
            simp only [hq]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this.2 hη') (by positivity)) 2
    have iC : IntegrableOn (fun a => condMom d (delF D c d) 2 a ^ 2) K (muI n) := by
      refine Integrable.of_bound ((measurable_condMom d mD 2).pow_const 2).aestronglyMeasurable
        ((L ^ 2) ^ 2) (ae_restrict_of_forall_mem mK fun a ha => ?_)
      obtain ⟨b0, b1⟩ := condMom_bounds d mD hvD (hKβ a ha) (hbD a ha) two_ne_zero
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ b0 b1 2
    calc ∫ a in K, condMom d (delF D c d) 2 a ^ 2 ∂muI n ≤ ∫ a in K, q a ^ 2 ∂muI n :=
          setIntegral_mono_on iC iq.integrableOn mK hqa
      _ ≤ ∫ a, q a ^ 2 ∂muI n :=
          setIntegral_le_integral iq (Filter.Eventually.of_forall fun a => sq_nonneg _)
      _ = (CA / σl ^ 2 * (1 - η)⁻¹) ^ 2 *
            ∫ a, (∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν) ^ 2 ∂muI n := by
          rw [← integral_const_mul]; congr 1; funext a; simp only [hq]; ring
      _ ≤ (CA / σl ^ 2 * (1 - η)⁻¹) ^ 2 * Vl ^ 2 := mul_le_mul_of_nonneg_left hVl (sq_nonneg _)
      _ = _ := by ring
  -- (Ie_k)
  have Ie : ∀ k : ℕ, k ≠ 0 → ∀ τ : ℝ, 0 < τ →
      ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ (2 * k) ∂ν ∂muI n ≤ τ ^ (2 * k) →
      ∫ a in K, condMom d (epsF D c d) (2 * k) a ∂muI n ≤
        (cEw ws σl * ((iotaP η (2 * k) + c2η η + c3η η ws σl) * τ)) ^ (2 * k) := by
    intro k hk τ hτ hMτ
    have hp : 2 * k ≠ 0 := by omega
    refine int_three (muI n) mK (mMs (2 * k)) (msd (fun a v => sgA D c a v - gbar D c a) mVs)
      (Kb := Ks ^ (2 * k) + Ks) (fun a => ?_) (fun a => ?_) ?_ (fun a => (bMs _ a).1)
      (fun a => Real.sqrt_nonneg _) (fun a => ?_) hcE (iotaP_pos h1 _) (iotaP_pow h1 hp) hc2 hc3
      hτ (fun a ha => ?_) hMτ
    · rw [abs_of_nonneg (bMs _ a).1]; linarith [(bMs (2 * k) a).2]
    · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      have : √(∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν) ≤ Ks := by
        rw [show Ks = √(Ks ^ 2) from (Real.sqrt_sq hKs0).symm]; exact Real.sqrt_le_sqrt (bVs a).2
      have : 0 ≤ Ks ^ (2 * k) := pow_nonneg hKs0 _
      linarith
    · refine Integrable.of_bound (measurable_condMom d mE _).aestronglyMeasurable
        (eps0 ws σl ^ (2 * k)) (ae_restrict_of_forall_mem mK fun a ha => ?_)
      obtain ⟨b0, b1⟩ := condMom_bounds d mE hvE (hKβ a ha) (hbE a ha) hp
      rw [Real.norm_eq_abs, abs_of_nonneg b0]; exact b1
    · rw [sd_pow (bVs a).1]
      have := jensen_pow ν (((mS a).sub_const (gbar D c a))) (bYs a) k
      simpa using this
    · obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
      rw [cm_eps hn D c h0 h1 ha hp]
      exact idx_eps_mom (measurableSet_slice d a) hm (mS a) (bS a) hws.le hσl hGψ hm1 h1 (2 * k)
        (mul_pos (iotaP_pos h1 _) hτ) (mul_pos hc2 hτ) (mul_pos hc3 hτ)
  -- (Id_k)
  have Id : ∀ k : ℕ, k ≠ 0 → ∀ τ : ℝ, 0 < τ →
      ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ (2 * k) ∂ν ∂muI n ≤ τ ^ (2 * k) →
      ∫ a in K, condMom d (delF D c d) (2 * k) a ∂muI n ≤
        (√CA / σl * ((iotaP η (2 * k) + c2η η) * τ)) ^ (2 * k) := by
    intro k hk τ hτ hMτ
    have hp : 2 * k ≠ 0 := by omega
    refine int_two (muI n) mK (mMl (2 * k)) (msd (fun a v => lA D c a v - lbar D c a) mVl)
      (Kb := Kl ^ (2 * k) + Kl) (fun a => ?_) (fun a => ?_) ?_ (fun a => (bMl _ a).1)
      (fun a => Real.sqrt_nonneg _) (fun a => ?_) (by positivity) (iotaP_pos h1 _)
      (iotaP_pow h1 hp) hc2 hτ (fun a ha => ?_) hMτ
    · rw [abs_of_nonneg (bMl _ a).1]; linarith [(bMl (2 * k) a).2]
    · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      have : √(∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν) ≤ Kl := by
        rw [show Kl = √(Kl ^ 2) from (Real.sqrt_sq hKl0).symm]; exact Real.sqrt_le_sqrt (bVl a).2
      have : 0 ≤ Kl ^ (2 * k) := pow_nonneg hKl0 _
      linarith
    · refine Integrable.of_bound (measurable_condMom d mD _).aestronglyMeasurable
        (L ^ (2 * k)) (ae_restrict_of_forall_mem mK fun a ha => ?_)
      obtain ⟨b0, b1⟩ := condMom_bounds d mD hvD (hKβ a ha) (hbD a ha) hp
      rw [Real.norm_eq_abs, abs_of_nonneg b0]; exact b1
    · rw [sd_pow (bVl a).1]
      have := jensen_pow ν (((mLa a).sub_const (lbar D c a))) (bYl a) k
      simpa using this
    · obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
      have hS0 : σl ^ 2 ≤ ∫ w, sgA D c a w ^ 2 ∂nrm ν (slice d a) := hS ▸ (hwin a ha).1
      rw [cm_del hn D c h0 h1 ha hp]
      have h := idx_del_mom (measurableSet_slice d a) hm (mLa a) (bLa a) hσl hS0
        (normSq_nonneg c.2.1.2) hm1 h1 (2 * k) (mul_pos (iotaP_pos h1 (2 * k)) hτ) (mul_pos hc2 hτ)
      refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right
          (Real.sqrt_le_sqrt hCA) hσl.le) _)
          (pow_nonneg (add_pos (mul_pos (iotaP_pos h1 (2 * k)) hτ) (mul_pos hc2 hτ)).le _)) ?_)
      have := (bMl (2 * k) a).1
      have : 0 < iotaP η (2 * k) * τ := mul_pos (iotaP_pos h1 _) hτ
      have : 0 < c2η η * τ := mul_pos hc2 hτ
      have : (0 : ℝ) ≤ (1 - η)⁻¹ := inv_nonneg.mpr (by linarith)
      positivity
  have hi8 := iotaP_pos h1 8
  have hi12 := iotaP_pos h1 12
  exact fluct_of_moments_hq D t c d hε0 hε (by positivity) hL0 (by positivity) hcA
    (fun a ha => ⟨(hwin a ha).1, fun v hv => ⟨((hwin a ha).2 v hv).1, ((hwin a ha).2 v hv).2.1,
      ((hwin a ha).2 v hv).2.2⟩⟩) hcent
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hB hD IA ID (Ie 4 (by norm_num) ts8 hts8 hs8) (Id 4 (by norm_num) tl8 htl8 hl8)
    (Ie 6 (by norm_num) ts12 hts12 hs12) (Id 6 (by norm_num) tl12 htl12 hl12) hl0 hl1 hl0' hl1' hsum


/-- **Part 162's `fluct_paper_mom` with Lemma HQ** (conclusion `FLUCT_hyp`). -/
theorem fluct_paper_mom_hq (hn : 1 ≤ n) (D : Design n) (c : Ret n) (t : ℝ) {wl ws σl η : ℝ} (hwl : 0 < wl)
    (hws : 0 < ws) (hσl : 0 < σl) (h0 : 0 < η) (h1 : η < 1) (hcA : 0 < normSq c.2.1.2)
    {CA : ℝ} (hCA : normSq c.2.1.2 ≤ CA) (hε : eps0 ws σl < 1)
    {Vs Vl VS ts8 ts12 tl8 tl12 tlq tsq βlow hfl : ℝ} (q : ℕ) (hVs0 : 0 ≤ Vs) (hVl0 : 0 ≤ Vl)
    (hVS0 : 0 ≤ VS) (hts8 : 0 < ts8) (hts12 : 0 < ts12) (htl8 : 0 < tl8) (htl12 : 0 < tl12)
    (htlq : 0 ≤ tlq) (htsq : 0 ≤ tsq) (hβl : 0 ≤ βlow)
    (hVs : ∫ a, (∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ Vs ^ 2)
    (hVl : ∫ a, (∫ v, (lA D c a v - lbar D c a) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ Vl ^ 2)
    (hVS : ∫ a, (∫ v, (sA D c a v - ∫ w, sA D c a w ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ VS ^ 2)
    (hs8 : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ ts8 ^ 8)
    (hs12 : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ ts12 ^ 12)
    (hl8 : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tl8 ^ 8)
    (hl12 : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tl12 ^ 12)
    (hlq : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ q ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tlq ^ q)
    (hsq : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ q ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tsq ^ q)
    (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA D c a v < σl} ∂muI n ≤ βlow)
    {lam lam' : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hl0' : 0 < lam') (hl1' : lam' < 1)
    (hsum : √(2 * (1 + η⁻¹) * Bpap wl ws tlq tsq βlow q) +
        √(priceC (1 - eps0 ws σl ^ 2)⁻¹ n (√CA * (2 * wl) / σl)
        (eps0 ws σl) (exp ((1 - eps0 ws σl ^ 2)⁻¹ * (n * eps0 ws σl ^ 2 / 2 +
          (√CA * (2 * wl) / σl) ^ 2 * (1 + eps0 ws σl))))
        (cVw ws σl * ((1 - η)⁻¹ * Vs)) (CA / σl ^ 2 * ((1 - η)⁻¹ * Vl))
        (cEw ws σl * ((iotaP η 8 + c2η η + c3η η ws σl) * ts8))
        (√CA / σl * ((iotaP η 8 + c2η η) * tl8))
        (cEw ws σl * ((iotaP η 12 + c2η η + c3η η ws σl) * ts12))
        (√CA / σl * ((iotaP η 12 + c2η η) * tl12)) / 4 +
        3 / 4 * cubP n (eps0 ws σl) lam lam' (cVw ws σl * ((1 - η)⁻¹ * Vs))
          (CA / σl ^ 2 * ((1 - η)⁻¹ * Vl))
          (cEw ws σl * ((iotaP η 12 + c2η η + c3η η ws σl) * ts12))
          (√CA / σl * ((iotaP η 12 + c2η η) * tl12))) +
        √(Dpap n (Bpap wl ws tlq tsq βlow q) CA Vl VS η σl) ≤ hfl) :
    FLUCT_hyp D t c (dPaper D c wl ws σl η h0 h1) hfl := by
  have hB := int_removed hn D c hwl hws q hlq hsq hmass (σl := σl)
  have hB0 : 0 ≤ Bpap wl ws tlq tsq βlow q := by unfold Bpap; positivity
  have hD := int_disp hn D c h0 h1 hσl hCA hB0 hVl0 hVS0 hB hVl hVS (wl := wl) (ws := ws)
  exact fluct_paper_hq hn D c t hwl.le hws hσl h0 h1 hcA hCA hε hVs0 hVl0 hts8 hts12 htl8 htl12
    hVs hVl hs8 hs12 hl8 hl12 hB hD hl0 hl1 hl0' hl1' hsum


/-- **Lemma HQ in the latitude-moment interface** (Part 162's `fluct_of_latMom` with the root
`rootFLH`; conclusion `FLUCT_hyp`). -/
theorem fluct_of_latMom_hq (hn : 1 ≤ n) (D : Design n) (c : Ret n) (t : ℝ) {wl ws σl η : ℝ}
    (hwl : 0 < wl) (hws : 0 < ws) (hσl : 0 < σl) (h0 : 0 < η) (h1 : η < 1)
    (hcA : 0 < normSq c.2.1.2) {CA : ℝ} (hCA : normSq c.2.1.2 ≤ CA) (hε : eps0 ws σl < 1) {q : ℕ}
    (P : LatMom D c σl q) {lam lam' : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hl0' : 0 < lam')
    (hl1' : lam' < 1) {hfl : ℝ} (hsum : rootFLH wl ws η CA lam lam' P ≤ hfl) :
    FLUCT_hyp D t c (dPaper D c wl ws σl η h0 h1) hfl :=
  fluct_paper_mom_hq hn D c t hwl hws hσl h0 h1 hcA hCA hε q P.hVs0 P.hVl0 P.hVS0 P.hts8 P.hts12
    P.htl8 P.htl12 P.htlq P.htsq P.hβl P.hVs P.hVl P.hVS P.hs8 P.hs12 P.hl8 P.hl12 P.hlq P.hsq
    P.hmass hl0 hl1 hl0' hl1' hsum

end BstLean.Part180
