import BstLean.Part161Chi

/-!
# Part 161, items 1(c) and 2: the fluctuation hypothesis in terms of the scalar fluctuations

Role: `delegations/statements/p161-spec.md`. Do not use `sorry`, `native_decide` or `axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Lemma `t7:p07:split` (the term
`√(E_s χ²(P_s^g ‖ Q_s))`), Lemma `t7:p07:chi-identity`, Proposition `t7:p07:FL`.

At an index `a` (the pair `(Z, G)` that gives the latitude), the good slice is
`s_a = {v | (a, v) ∈ good}`, with mass `1 − β(a)`. The normalized good-set mixture is
`P_a^g = E[N(λ(x) c_A, S(x) I) | a, good]`, `x = xLat c (latitude a) (v/|v|)`. The reference is
`Q_a = N(λ₀(a) c_A, S₀(a) I)`. With `δ = λ(x) − λ₀(a)`, `ε = S(x)/S₀(a) − 1`,
`a² = |c_A|²/S₀(a)`:

* `chiK D c d a = (1 − β(a))^{−2}·E_{ν⊗ν}[1_{s_a}(v) 1_{s_a}(v') kTwo n a² δ ε δ' ε'] − 1`: the
  two-copy form of `χ²(P_a^g ‖ Q_a)` (an expression in the scalar fluctuations `(δ, ε)` on the
  good set).
* `root_le_chiK`: on a kept index with the window `|ε| ≤ ε₀ < 1`, `|δ| ≤ δ₀` on the good slice:
  `(√P_a^g(C) − √Q_a(C))² ≤ chiK D c d a`.
* `FLUCT_chi_hyp`: the fluctuation hypothesis with `chiK` (scalar moments of `(δ, ε)`).
* **`fluct_of_chi`**: `FLUCT_chi_hyp → FLUCT_hyp`; **`repla_of_hyps_chi`**: `REPLA_mix_hyp`
  from `FLUCT_chi_hyp`, `BIAS_hyp` and the World window.
-/

namespace BstLean.Part161

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157
open BstLean.Part53 (unitF53 measurable_unitF)

variable {n : ℕ}

/-- The good slice `s_a = {v | (a, v) ∈ good}` at the index `a`. -/
def slice (d : SplitData n) (a : Ix n) : Set (Fin (n - 1) → ℝ) := {v | (a, v) ∈ d.good}

lemma measurableSet_slice (d : SplitData n) (a : Ix n) : MeasurableSet (slice d a) :=
  d.mgood.preimage measurable_prodMk_left

/-- `λ(x)` at the pair `(a, v)`. -/
noncomputable def lA (D : Design n) (c : Ret n) (a : Ix n) (v : Fin (n - 1) → ℝ) : ℝ :=
  lamX D c (xLat c (latC D c a) (unitF53 v))

/-- `S(x) = σ(x)²` at the pair `(a, v)`. -/
noncomputable def sA (D : Design n) (c : Ret n) (a : Ix n) (v : Fin (n - 1) → ℝ) : ℝ :=
  sigX D c (xLat c (latC D c a) (unitF53 v)) ^ 2

lemma measurable_xA (D : Design n) (c : Ret n) :
    Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => xLat c (latC D c p.1) (unitF53 p.2)) :=
  measurable_xLat_comp c ((measurable_latC D c).comp measurable_fst)
    (measurable_unitF.comp measurable_snd)

lemma measurable_lA (D : Design n) (c : Ret n) :
    Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => lA D c p.1 p.2) :=
  (measurable_lamX D c).comp (measurable_xA D c)

lemma measurable_sA (D : Design n) (c : Ret n) :
    Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => sA D c p.1 p.2) :=
  ((measurable_sigX D c).comp (measurable_xA D c)).pow_const 2

lemma measurable_lA_left (D : Design n) (c : Ret n) (a : Ix n) : Measurable (lA D c a) :=
  (measurable_lamX D c).comp (measurable_xLat_comp c measurable_const measurable_unitF)

lemma measurable_sA_left (D : Design n) (c : Ret n) (a : Ix n) : Measurable (sA D c a) :=
  ((measurable_sigX D c).comp (measurable_xLat_comp c measurable_const measurable_unitF)).pow_const 2

lemma measurable_lA_comp {β : Type*} [MeasurableSpace β] (D : Design n) (c : Ret n)
    {f : β → Ix n} {g : β → Fin (n - 1) → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => lA D c (f x) (g x)) :=
  (measurable_lamX D c).comp (measurable_xLat_comp c ((measurable_latC D c).comp hf)
    (measurable_unitF.comp hg))

lemma measurable_sA_comp {β : Type*} [MeasurableSpace β] (D : Design n) (c : Ret n)
    {f : β → Ix n} {g : β → Fin (n - 1) → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => sA D c (f x) (g x)) :=
  ((measurable_sigX D c).comp (measurable_xLat_comp c ((measurable_latC D c).comp hf)
    (measurable_unitF.comp hg))).pow_const 2

/-- The integral `E_{ν⊗ν}[1_{s_a}(v) 1_{s_a}(v') kTwo n a² δ ε δ' ε']`. -/
noncomputable def kChiInt (D : Design n) (c : Ret n) (d : SplitData n) (a : Ix n) : ℝ :=
  ∫ w, (slice d a).indicator 1 w.1 * (slice d a).indicator 1 w.2 *
    kTwo n (normSq c.2.1.2 / d.S0 a) (lA D c a w.1 - d.lam0 a) (sA D c a w.1 / d.S0 a - 1)
      (lA D c a w.2 - d.lam0 a) (sA D c a w.2 / d.S0 a - 1)
    ∂((stdGauss (Fin (n - 1))).prod (stdGauss (Fin (n - 1))))

/-- **The chi-square of the good-set mixture against the reference, in two-copy form**:
`chiK = (1 − β(a))^{−2}·kChiInt − 1` (Lemma `t7:p07:chi-identity`: `1 + χ² = E e^T` for two
independent copies of the good-set parameters). -/
noncomputable def chiK (D : Design n) (c : Ret n) (d : SplitData n) (a : Ix n) : ℝ :=
  ((1 - removed (stdGauss (Fin (n - 1))) d.good a)⁻¹) ^ 2 * kChiInt D c d a - 1

/-- **The root bound by the two-copy chi-square at one kept index.** If the removed mass is
`β(a) < 1`, `S₀(a) > 0`, `0 ≤ ε₀ < 1`, `0 ≤ δ₀`, and on the good slice
`|S(x)/S₀(a) − 1| ≤ ε₀`, `|λ(x) − λ₀(a)| ≤ δ₀`, THEN
`(√P_a^g(C) − √Q_a(C))² ≤ chiK D c d a` for the classifier event `C`. -/
theorem root_le_chiK (D : Design n) (t : ℝ) (c : Ret n) (d : SplitData n) (a : Ix n)
    (hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1) (hS0 : 0 < d.S0 a) {ε₀ δ₀ : ℝ}
    (hε0 : 0 ≤ ε₀) (hε₀ : ε₀ < 1) (hδ0 : 0 ≤ δ₀)
    (hw : ∀ v ∈ slice d a, |sA D c a v / d.S0 a - 1| ≤ ε₀ ∧ |lA D c a v - d.lam0 a| ≤ δ₀) :
    (√(goodMean (stdGauss (Fin (n - 1))) d.good (pLat D t c) a) - √(q0Lat t c d a)) ^ 2 ≤
      chiK D c d a := by
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
  have hmain := mix_root_chi piG c.2.1.2 (measurableSet_clsSet c t) hS0 ml' mS' hε₀ hwS hwl
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

lemma measurable_kChiInt (D : Design n) (c : Ret n) (d : SplitData n) :
    Measurable (kChiInt D c d) := by
  set ν := stdGauss (Fin (n - 1))
  have mI1 : Measurable (fun p : Ix n × ((Fin (n - 1) → ℝ) × (Fin (n - 1) → ℝ)) =>
      (slice d p.1).indicator (1 : (Fin (n - 1) → ℝ) → ℝ) p.2.1) := by
    have e : (fun p : Ix n × ((Fin (n - 1) → ℝ) × (Fin (n - 1) → ℝ)) =>
        (slice d p.1).indicator (1 : (Fin (n - 1) → ℝ) → ℝ) p.2.1) =
        fun p => d.good.indicator (1 : Ix n × (Fin (n - 1) → ℝ) → ℝ) (p.1, p.2.1) := by
      funext p; simp only [Set.indicator, slice, Pi.one_apply]; rfl
    rw [e]
    exact (measurable_one.indicator d.mgood).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have mI2 : Measurable (fun p : Ix n × ((Fin (n - 1) → ℝ) × (Fin (n - 1) → ℝ)) =>
      (slice d p.1).indicator (1 : (Fin (n - 1) → ℝ) → ℝ) p.2.2) := by
    have e : (fun p : Ix n × ((Fin (n - 1) → ℝ) × (Fin (n - 1) → ℝ)) =>
        (slice d p.1).indicator (1 : (Fin (n - 1) → ℝ) → ℝ) p.2.2) =
        fun p => d.good.indicator (1 : Ix n × (Fin (n - 1) → ℝ) → ℝ) (p.1, p.2.2) := by
      funext p; simp only [Set.indicator, slice, Pi.one_apply]; rfl
    rw [e]
    exact (measurable_one.indicator d.mgood).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have ml1 : Measurable (fun p : Ix n × ((Fin (n - 1) → ℝ) × (Fin (n - 1) → ℝ)) =>
      lA D c p.1 p.2.1) :=
    measurable_lA_comp D c measurable_fst (measurable_fst.comp measurable_snd)
  have ml2 : Measurable (fun p : Ix n × ((Fin (n - 1) → ℝ) × (Fin (n - 1) → ℝ)) =>
      lA D c p.1 p.2.2) :=
    measurable_lA_comp D c measurable_fst (measurable_snd.comp measurable_snd)
  have ms1 : Measurable (fun p : Ix n × ((Fin (n - 1) → ℝ) × (Fin (n - 1) → ℝ)) =>
      sA D c p.1 p.2.1) :=
    measurable_sA_comp D c measurable_fst (measurable_fst.comp measurable_snd)
  have ms2 : Measurable (fun p : Ix n × ((Fin (n - 1) → ℝ) × (Fin (n - 1) → ℝ)) =>
      sA D c p.1 p.2.2) :=
    measurable_sA_comp D c measurable_fst (measurable_snd.comp measurable_snd)
  have mS0 : Measurable (fun p : Ix n × ((Fin (n - 1) → ℝ) × (Fin (n - 1) → ℝ)) => d.S0 p.1) :=
    d.mS0.comp measurable_fst
  have ml0 : Measurable (fun p : Ix n × ((Fin (n - 1) → ℝ) × (Fin (n - 1) → ℝ)) => d.lam0 p.1) :=
    d.mlam0.comp measurable_fst
  have mK : Measurable (fun p : Ix n × ((Fin (n - 1) → ℝ) × (Fin (n - 1) → ℝ)) =>
      kTwo n (normSq c.2.1.2 / d.S0 p.1) (lA D c p.1 p.2.1 - d.lam0 p.1)
        (sA D c p.1 p.2.1 / d.S0 p.1 - 1) (lA D c p.1 p.2.2 - d.lam0 p.1)
        (sA D c p.1 p.2.2 / d.S0 p.1 - 1)) :=
    (measurable_kTwo n).comp ((measurable_const.div mS0).prodMk
      (((ml1.sub ml0).prodMk ((ms1.div mS0).sub_const 1)).prodMk
        ((ml2.sub ml0).prodMk ((ms2.div mS0).sub_const 1))))
  have mH := (mI1.mul mI2).mul mK
  exact (mH.stronglyMeasurable.integral_prod_right' (ν := ν.prod ν)).measurable

lemma measurable_chiK (D : Design n) (c : Ret n) (d : SplitData n) : Measurable (chiK D c d) := by
  unfold chiK
  exact (((measurable_const.sub (measurable_removed _ d.mgood)).inv.pow_const 2).mul
    (measurable_kChiInt D c d)).sub_const 1

/-- **(FLUCT) in terms of the scalar fluctuations of `(λ, S)` on the good set.** The window:
`0 ≤ ε₀ < 1`, `δ₀ ≥ 0`, and on every kept index `a`: `S₀(a) ≥ s_low > 0`, and on the good slice
`|S(x)/S₀(a) − 1| ≤ ε₀`, `|λ(x) − λ₀(a)| ≤ δ₀`. The moments: there are `B`, `C`, `Dd` with
`E β ≤ B`, `E_kept chiK ≤ C` (the two-copy chi-square of the good-set mixture against the
good-set reference), `E_kept H²(Q_a, Q̄_a) ≤ Dd`, and `√(2(1 + 1/η)B) + √C + √Dd ≤ h_fl`.

Paper statement that proves it: `theorem7-07-mixture-fluctuation.tex`, Proposition `t7:p07:FL`
(the good set `𝒳_s`, the window `ε₀ = (1 + 2d_w/√d_low)² − 1`, `|a_c δ| ≤ L`, the price `𝒞` from
Corollary `t7:p07:chi-bounds`, the price `𝒟`, the removed mass `B`; `h_fl < 0.002159`). -/
def FLUCT_chi_hyp (D : Design n) (c : Ret n) (d : SplitData n) (ε₀ δ₀ slow hfl : ℝ) : Prop :=
  0 ≤ ε₀ ∧ ε₀ < 1 ∧ 0 ≤ δ₀ ∧ 0 < slow ∧
    (∀ a ∈ keptIx D c d, slow ≤ d.S0 a ∧ ∀ v ∈ slice d a,
      |sA D c a v / d.S0 a - 1| ≤ ε₀ ∧ |lA D c a v - d.lam0 a| ≤ δ₀) ∧
    ∃ B C Dd : ℝ,
      ∫ a, removed (stdGauss (Fin (n - 1))) d.good a ∂muI n ≤ B ∧
      ∫ a in keptIx D c d, chiK D c d a ∂muI n ≤ C ∧
      ∫ a in keptIx D c d, hellG2 n ((d.lam0 a - d.lamb a) ^ 2 * normSq c.2.1.2) (d.S0 a) (d.Sb a)
        ∂muI n ≤ Dd ∧
      √(2 * (1 + d.eta⁻¹) * B) + √C + √Dd ≤ hfl

/-- On a kept index in the window, `chiK` is bounded: `−1 ≤ chiK ≤ M`. -/
lemma chiK_bounds (D : Design n) (c : Ret n) (d : SplitData n) {ε₀ δ₀ slow : ℝ}
    (hε0 : 0 ≤ ε₀) (hε₀ : ε₀ < 1) (hslow : 0 < slow) (a : Ix n)
    (hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1) (hS0 : slow ≤ d.S0 a)
    (hw : ∀ v ∈ slice d a, |sA D c a v / d.S0 a - 1| ≤ ε₀ ∧ |lA D c a v - d.lam0 a| ≤ δ₀) :
    -1 ≤ chiK D c d a ∧ chiK D c d a ≤
      (√(1 - ε₀ ^ 2))⁻¹ ^ n * exp ((1 + ε₀) * (normSq c.2.1.2 / slow) * δ₀ ^ 2 / (1 - ε₀ ^ 2)) := by
  set ν := stdGauss (Fin (n - 1))
  set s := slice d a
  have ms : MeasurableSet s := measurableSet_slice d a
  set m := 1 - removed ν d.good a with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hνs : ν.real s = m := by
    have h1 : removed ν d.good a = ν.real sᶜ := rfl
    rw [hm, h1, measureReal_compl ms, probReal_univ]
    ring
  have hS0p : 0 < d.S0 a := lt_of_lt_of_le hslow hS0
  set M := (√(1 - ε₀ ^ 2))⁻¹ ^ n * exp ((1 + ε₀) * (normSq c.2.1.2 / slow) * δ₀ ^ 2 / (1 - ε₀ ^ 2))
  have hd0 : 0 < 1 - ε₀ ^ 2 := by nlinarith
  have hM0 : 0 ≤ M := mul_nonneg (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _) (exp_pos _).le
  set H : (Fin (n - 1) → ℝ) × (Fin (n - 1) → ℝ) → ℝ := fun w =>
    s.indicator 1 w.1 * s.indicator 1 w.2 *
      kTwo n (normSq c.2.1.2 / d.S0 a) (lA D c a w.1 - d.lam0 a) (sA D c a w.1 / d.S0 a - 1)
        (lA D c a w.2 - d.lam0 a) (sA D c a w.2 / d.S0 a - 1) with hH
  have ind01 : ∀ v, s.indicator (1 : (Fin (n - 1) → ℝ) → ℝ) v = 0 ∨
      s.indicator (1 : (Fin (n - 1) → ℝ) → ℝ) v = 1 := fun v => by
    by_cases h : v ∈ s <;> simp [h]
  have H0 : ∀ w, 0 ≤ H w := fun w => by
    refine mul_nonneg (mul_nonneg ?_ ?_) (kTwo_nonneg _ _ _ _ _ _) <;>
    · rcases ind01 _ with h | h <;> rw [h] <;> norm_num
  have HM : ∀ w, H w ≤ M * (s.indicator 1 w.1 * s.indicator 1 w.2) := fun w => by
    by_cases h1 : w.1 ∈ s
    · by_cases h2 : w.2 ∈ s
      · simp only [hH, Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply, one_mul,
          mul_one]
        refine (kTwo_le n (div_nonneg (normSq_nonneg _) hS0p.le) hε₀ (hw _ h1).1 (hw _ h2).1
          (hw _ h1).2 (hw _ h2).2).trans ?_
        refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_)
          (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
        refine div_le_div_of_nonneg_right ?_ hd0.le
        have : normSq c.2.1.2 / d.S0 a ≤ normSq c.2.1.2 / slow :=
          div_le_div_of_nonneg_left (normSq_nonneg _) hslow hS0
        have h1e : 0 ≤ 1 + ε₀ := by linarith
        have := mul_le_mul_of_nonneg_left this h1e
        nlinarith [sq_nonneg δ₀]
      · simp [hH, Set.indicator_of_notMem h2]
    · simp [hH, Set.indicator_of_notMem h1]
  have mH : Measurable H := by
    have mI : Measurable (s.indicator (1 : (Fin (n - 1) → ℝ) → ℝ)) := measurable_one.indicator ms
    have ml := measurable_lA_left D c a
    have mS := measurable_sA_left D c a
    exact ((mI.comp measurable_fst).mul (mI.comp measurable_snd)).mul
      ((measurable_kTwo n).comp (measurable_const.prodMk
        ((((ml.comp measurable_fst).sub_const _).prodMk
          (((mS.comp measurable_fst).div_const _).sub_const 1)).prodMk
          (((ml.comp measurable_snd).sub_const _).prodMk
            (((mS.comp measurable_snd).div_const _).sub_const 1)))))
  have iI : Integrable (fun w : (Fin (n - 1) → ℝ) × (Fin (n - 1) → ℝ) =>
      s.indicator (1 : (Fin (n - 1) → ℝ) → ℝ) w.1 * s.indicator 1 w.2) (ν.prod ν) := by
    refine Integrable.of_bound (((measurable_one.indicator ms).comp measurable_fst).mul
      ((measurable_one.indicator ms).comp measurable_snd)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun w => ?_)
    rcases ind01 w.1 with h | h <;> rcases ind01 w.2 with h' | h' <;> simp [h, h']
  have iH : Integrable H (ν.prod ν) := by
    refine Integrable.mono' (iI.const_mul M) mH.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (H0 w)]
    exact HM w
  have hII : ∫ w, s.indicator (1 : (Fin (n - 1) → ℝ) → ℝ) w.1 * s.indicator 1 w.2 ∂(ν.prod ν) =
      m * m := by
    rw [integral_prod_mul (fun v => s.indicator (1 : (Fin (n - 1) → ℝ) → ℝ) v)
      (fun v => s.indicator (1 : (Fin (n - 1) → ℝ) → ℝ) v), integral_indicator_one ms, hνs]
  have hK0 : 0 ≤ kChiInt D c d a := integral_nonneg H0
  have hK1 : kChiInt D c d a ≤ M * (m * m) := by
    have := integral_mono iH (iI.const_mul M) HM
    rw [integral_const_mul, hII] at this
    exact this
  unfold chiK
  have hinv : 0 < (m⁻¹) ^ 2 := by positivity
  constructor
  · have := mul_nonneg hinv.le hK0
    linarith
  · have h2 : (m⁻¹) ^ 2 * kChiInt D c d a ≤ (m⁻¹) ^ 2 * (M * (m * m)) :=
      mul_le_mul_of_nonneg_left hK1 hinv.le
    have h3 : (m⁻¹) ^ 2 * (M * (m * m)) = M := by field_simp
    linarith

/-- **`FLUCT_chi_hyp` gives `FLUCT_hyp`** (the two-copy identity on every kept latitude). -/
theorem fluct_of_chi (D : Design n) (t : ℝ) (c : Ret n) (d : SplitData n) {ε₀ δ₀ slow hfl : ℝ}
    (h : FLUCT_chi_hyp D c d ε₀ δ₀ slow hfl) : FLUCT_hyp D t c d hfl := by
  obtain ⟨hε0, hε₀, hδ0, hslow, hwin, B, C, Dd, hB, hC, hD, hsum⟩ := h
  refine ⟨B, C, Dd, hB, ?_, hD, hsum⟩
  set ν := stdGauss (Fin (n - 1))
  set K := keptIx D c d
  have mK : MeasurableSet K :=
    measurableSet_keptSet ν d.mgood (measurableSet_bulkIx D c) d.eta
  have hKβ : ∀ a ∈ K, removed ν d.good a < 1 := fun a ha => lt_of_le_of_lt ha.2 d.eta_lt
  have mpl := measurable_pLat D t c
  have hpl0 : ∀ q, 0 ≤ pLat D t c q := fun q => gP_nonneg _ _ _
  have hpl1 : ∀ q, pLat D t c q ≤ 1 := fun q => gP_le_one _ _ _
  have mq0 : Measurable (q0Lat t c d) :=
    measurable_gP_comp (measurableSet_clsSet c t) (d.mlam0.smul_const _) d.mS0
  have mX : Measurable (fun a => (√(goodMean ν d.good (pLat D t c) a) - √(q0Lat t c d a)) ^ 2) :=
    (((measurable_goodMean ν d.mgood mpl).sqrt).sub mq0.sqrt).pow_const 2
  set M := (√(1 - ε₀ ^ 2))⁻¹ ^ n * exp ((1 + ε₀) * (normSq c.2.1.2 / slow) * δ₀ ^ 2 / (1 - ε₀ ^ 2))
  have iX : IntegrableOn (fun a => (√(goodMean ν d.good (pLat D t c) a) - √(q0Lat t c d a)) ^ 2)
      K (muI n) := by
    refine Integrable.of_bound mX.aestronglyMeasurable 1 (ae_restrict_of_forall_mem mK fun a ha => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨h0, h1, _⟩ := goodMean_bounds ν d.mgood mpl hpl0 hpl1 a (hKβ a ha)
    exact sqrt_sub_sq_le_one h0 h1 (gP_nonneg _ _ _) (gP_le_one _ _ _)
  have iC : IntegrableOn (chiK D c d) K (muI n) := by
    refine Integrable.of_bound (measurable_chiK D c d).aestronglyMeasurable (M + 1)
      (ae_restrict_of_forall_mem mK fun a ha => ?_)
    obtain ⟨hS, hw⟩ := hwin a ha
    obtain ⟨b1, b2⟩ := chiK_bounds D c d hε0 hε₀ hslow a (hKβ a ha) hS hw
    have hM0 : 0 ≤ M :=
      mul_nonneg (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _) (exp_pos _).le
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  refine le_trans (setIntegral_mono_on iX iC mK fun a ha => ?_) hC
  obtain ⟨hS, hw⟩ := hwin a ha
  exact root_le_chiK D t c d a (hKβ a ha) (lt_of_lt_of_le hslow hS) hε0 hε₀ hδ0 hw

/-- **`REPLA_mix_hyp` from the scalar fluctuation hypothesis (items 1(c) and 2).** For
`n ≥ 16 384`: IF on `E` the World window holds and there are split data `d` and window constants
with `FLUCT_chi_hyp D c d ε₀ δ₀ s_low 0.002159` and `BIAS_hyp D c d 0.004295`, THEN
`REPLA_mix_hyp D t h_A E`, `h_A = 0.006583 + 10⁻²⁰`. -/
theorem repla_of_hyps_chi (hn : 16384 ≤ n) (D : Design n) (t : ℝ) {E : Set (Ret n)}
    (hw : ∀ c ∈ E, WINDOW D c)
    (hd : ∀ c ∈ E, ∃ (d : SplitData n) (ε₀ δ₀ slow : ℝ),
      FLUCT_chi_hyp D c d ε₀ δ₀ slow (2159 / 10 ^ 6) ∧ BIAS_hyp D c d (4295 / 10 ^ 6)) :
    REPLA_mix_hyp D t BstLean.Part156.hAL E := by
  refine repla_of_hyps hn D t hw fun c hc => ?_
  obtain ⟨d, ε₀, δ₀, slow, hF, hB⟩ := hd c hc
  exact ⟨d, fluct_of_chi D t c d hF, hB⟩

end BstLean.Part161

open BstLean.Part161 in
#print axioms root_le_chiK
open BstLean.Part161 in
#print axioms fluct_of_chi
open BstLean.Part161 in
#print axioms repla_of_hyps_chi
