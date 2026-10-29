import BstLean.Part161All
import BstLean.Part162Int

/-!
# Part 162, item 3: the chi-square part of Proposition FL from joint moments

Role: `delegations/statements/p162-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Corollary `t7:p07:chi-bounds`
(formula `t7:p07:chi-six`, applied "to two independent copies conditional on the same `s`"),
and the proof of Proposition `t7:p07:FL` (the price `𝒞`).

* `gMeas d a`: the normalized good-set measure on the slice of the index `a`.
* `eG`, `dG`: the fields `ε = S/S₀ − 1`, `δ = λ − λ₀` on the good slice (`0` off it).
* `chiK_eq_gMeas`: `chiK` is the two-copy integral of `kTwo` for `gMeas ⊗ gMeas`.
* **`chiK_le_sixF`**: on one kept index, with centred references and the window
  `|ε| ≤ ε₀`, `a_c²δ² ≤ L²`: `chiK ≤ sixF` in the moment norms of `ε`, `a_c δ`
  (Part 161's `chi_six` with `δ₀ = L/a_c`). This is the per-latitude application of
  `chi_six` that Part 161 did not do.
* `condMom d F k a = (1 − β(a))^{−1} ∫ |F(a, v)|^k dν(v)`: good-conditional moments;
  `epsF`, `delF` the fields `ε`, `a_c δ` as functions of `(a, v)`.
* **`fluct_of_moments`**: `FLUCT_chi_hyp` from the window, the centring, `B`, `Dd`, and the joint
  moments `A`, `D`, `e₄`, `d₄`, `e₆`, `d₆` (with `√(2(1 + 1/η)B) + √𝒞 + √Dd ≤ h_fl`).
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157
open BstLean.Part161
open BstLean.Part53 (unitF53 measurable_unitF)

variable {n : ℕ}

/-- The normalized good-set measure on the slice of the index `a`:
`(1 − β(a))^{−1}·ν|_{s_a}` (a probability measure when `β(a) < 1`). -/
noncomputable def gMeas (d : SplitData n) (a : Ix n) : Measure (Fin (n - 1) → ℝ) :=
  (ENNReal.ofReal (1 - removed (stdGauss (Fin (n - 1))) d.good a))⁻¹ •
    (stdGauss (Fin (n - 1))).restrict (slice d a)

lemma slice_real (d : SplitData n) (a : Ix n) :
    (stdGauss (Fin (n - 1))).real (slice d a) = 1 - removed (stdGauss (Fin (n - 1))) d.good a := by
  have h1 : removed (stdGauss (Fin (n - 1))) d.good a = (stdGauss (Fin (n - 1))).real (slice d a)ᶜ :=
    rfl
  rw [h1, measureReal_compl (measurableSet_slice d a), probReal_univ]
  ring

lemma isProb_gMeas (d : SplitData n) {a : Ix n}
    (hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1) : IsProbabilityMeasure (gMeas d a) := by
  constructor
  have hm0 : 0 < 1 - removed (stdGauss (Fin (n - 1))) d.good a := by linarith
  have hνs : stdGauss (Fin (n - 1)) (slice d a) =
      ENNReal.ofReal (1 - removed (stdGauss (Fin (n - 1))) d.good a) := by
    rw [← slice_real, ofReal_measureReal (measure_ne_top _ _)]
  rw [gMeas, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hνs,
    smul_eq_mul, ENNReal.inv_mul_cancel (by simpa using hm0) ENNReal.ofReal_ne_top]

lemma integral_gMeas (d : SplitData n) {a : Ix n}
    (hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1) (f : (Fin (n - 1) → ℝ) → ℝ) :
    ∫ v, f v ∂gMeas d a = (1 - removed (stdGauss (Fin (n - 1))) d.good a)⁻¹ *
      ∫ v, (slice d a).indicator f v ∂stdGauss (Fin (n - 1)) := by
  have hm0 : 0 < 1 - removed (stdGauss (Fin (n - 1))) d.good a := by linarith
  rw [gMeas, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal hm0.le,
    integral_indicator (measurableSet_slice d a), smul_eq_mul]

/-- `ε = S(x)/S₀(a) − 1` on the good slice, `0` off it. -/
noncomputable def eG (D : Design n) (c : Ret n) (d : SplitData n) (a : Ix n)
    (v : Fin (n - 1) → ℝ) : ℝ :=
  (slice d a).indicator (fun v => sA D c a v / d.S0 a - 1) v

/-- `δ = λ(x) − λ₀(a)` on the good slice, `0` off it. -/
noncomputable def dG (D : Design n) (c : Ret n) (d : SplitData n) (a : Ix n)
    (v : Fin (n - 1) → ℝ) : ℝ :=
  (slice d a).indicator (fun v => lA D c a v - d.lam0 a) v

lemma measurable_eG (D : Design n) (c : Ret n) (d : SplitData n) (a : Ix n) :
    Measurable (eG D c d a) :=
  (((measurable_sA_left D c a).div_const _).sub_const 1).indicator (measurableSet_slice d a)

lemma measurable_dG (D : Design n) (c : Ret n) (d : SplitData n) (a : Ix n) :
    Measurable (dG D c d a) :=
  ((measurable_lA_left D c a).sub_const _).indicator (measurableSet_slice d a)

/-- **`chiK` as the two-copy integral for the normalized good-set measure.** -/
theorem chiK_eq_gMeas (D : Design n) (c : Ret n) (d : SplitData n) {a : Ix n}
    (hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1) :
    chiK D c d a = ∫ w, kTwo n (normSq c.2.1.2 / d.S0 a) (dG D c d a w.1) (eG D c d a w.1)
      (dG D c d a w.2) (eG D c d a w.2) ∂((gMeas d a).prod (gMeas d a)) - 1 := by
  classical
  have := isProb_gMeas d hβ
  set ν := stdGauss (Fin (n - 1)) with hν
  set s := slice d a with hs
  have ms : MeasurableSet s := measurableSet_slice d a
  set m := 1 - removed ν d.good a with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  set k : ℝ≥0∞ := (ENNReal.ofReal m)⁻¹ with hk
  have hkr : k.toReal = m⁻¹ := by
    rw [hk, ENNReal.toReal_inv, ENNReal.toReal_ofReal hm0.le]
  have hprod : (gMeas d a).prod (gMeas d a) = (k * k) • (ν.prod ν).restrict (s ×ˢ s) := by
    rw [← Measure.prod_restrict]
    refine Measure.prod_eq fun A A' hA hA' => ?_
    rw [Measure.smul_apply, Measure.prod_prod, smul_eq_mul, gMeas, Measure.smul_apply,
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
        Set.indicator_of_mem (show w.2 ∈ slice d a from h2), dG, eG, Pi.one_apply, one_mul]
    · have h12 : w ∉ s ×ˢ s := fun h => h2 h.2
      simp only [Set.indicator_of_notMem h12,
        Set.indicator_of_notMem (show w.2 ∉ slice d a from h2), mul_zero, zero_mul]
  · have h12 : w ∉ s ×ˢ s := fun h => h1 h.1
    simp only [Set.indicator_of_notMem h12,
      Set.indicator_of_notMem (show w.1 ∉ slice d a from h1), zero_mul]


lemma momN_const_mul {V : Type*} [MeasurableSpace V] (pm : Measure V) {k : ℕ} (hk : k ≠ 0) (c : ℝ)
    (f : V → ℝ) : momN pm k (fun v => c * f v) = |c| * momN pm k f := by
  unfold momN
  have e : ∀ v, |c * f v| ^ k = |c| ^ k * |f v| ^ k := fun v => by rw [abs_mul, mul_pow]
  simp_rw [e]
  rw [integral_const_mul, Real.mul_rpow (pow_nonneg (abs_nonneg c) k)
    (integral_nonneg fun v => pow_nonneg (abs_nonneg _) _), Real.pow_rpow_inv_natCast (abs_nonneg c) hk]

/-- **The centred sixth-order bound applied on one kept index (Corollary `t7:p07:chi-bounds`
for the good-set mixture of one latitude).** Hypotheses: `β(a) < 1`, `S₀(a) > 0`, `|c_A| > 0`;
on the good slice, `|S(x)/S₀(a) − 1| ≤ ε₀ < 1` and `a_c²(λ(x) − λ₀(a))² ≤ L²`
(`a_c² = |c_A|²/S₀(a)`); the references are the good-set means (`λ₀(a) = E(λ | good)`,
`S₀(a) = E(S | good)`, written as `∫_{s_a}(λ − λ₀) = 0`, `∫_{s_a}(S/S₀ − 1) = 0`). THEN
`chiK ≤ sixF` with the scales `x_k = ‖ε‖_k`, `y_k = ‖a_c δ‖_k` of the normalized good-set
measure, `κ = (1 − ε₀²)^{−1}`, `E = exp(κ(nε₀²/2 + L²(1 + ε₀)))`. -/
theorem chiK_le_sixF (D : Design n) (c : Ret n) (d : SplitData n) {a : Ix n}
    (hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1) (hS0 : 0 < d.S0 a)
    (hcA : 0 < normSq c.2.1.2) {ε₀ L : ℝ} (hε0 : 0 ≤ ε₀) (hε₀ : ε₀ < 1) (hL : 0 ≤ L)
    (hw : ∀ v ∈ slice d a, |sA D c a v / d.S0 a - 1| ≤ ε₀ ∧
      normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2 ≤ L ^ 2)
    (hmδ : ∫ v in slice d a, (lA D c a v - d.lam0 a) ∂stdGauss (Fin (n - 1)) = 0)
    (hmε : ∫ v in slice d a, (sA D c a v / d.S0 a - 1) ∂stdGauss (Fin (n - 1)) = 0) :
    chiK D c d a ≤ sixF (1 - ε₀ ^ 2)⁻¹ n L ε₀
      (exp ((1 - ε₀ ^ 2)⁻¹ * (n * ε₀ ^ 2 / 2 + L ^ 2 * (1 + ε₀))))
      (momN (gMeas d a) 2 (eG D c d a))
      (momN (gMeas d a) 2 (fun v => √(normSq c.2.1.2 / d.S0 a) * dG D c d a v))
      (momN (gMeas d a) 4 (eG D c d a))
      (momN (gMeas d a) 4 (fun v => √(normSq c.2.1.2 / d.S0 a) * dG D c d a v))
      (momN (gMeas d a) 6 (eG D c d a))
      (momN (gMeas d a) 6 (fun v => √(normSq c.2.1.2 / d.S0 a) * dG D c d a v)) := by
  have hP := isProb_gMeas d hβ
  set pm := gMeas d a with hpm
  set a2 := normSq c.2.1.2 / d.S0 a with ha2d
  have ha2 : 0 < a2 := div_pos hcA hS0
  have hsa : 0 < √a2 := Real.sqrt_pos.mpr ha2
  set δ₀ := L / √a2 with hδ₀
  set κ := (1 - ε₀ ^ 2)⁻¹ with hκ
  have ms := measurableSet_slice d a
  have hwδ : ∀ v, |dG D c d a v| ≤ δ₀ := fun v => by
    by_cases hv : v ∈ slice d a
    · have h := (hw v hv).2
      simp only [dG, Set.indicator_of_mem hv]
      rw [hδ₀, le_div_iff₀ hsa]
      have h2 : √(a2 * (lA D c a v - d.lam0 a) ^ 2) ≤ √(L ^ 2) := Real.sqrt_le_sqrt h
      rwa [Real.sqrt_mul ha2.le, Real.sqrt_sq_eq_abs, Real.sqrt_sq hL, mul_comm] at h2
    · simp only [dG, Set.indicator_of_notMem hv, abs_zero]; positivity
  have hwε : ∀ v, |eG D c d a v| ≤ ε₀ := fun v => by
    by_cases hv : v ∈ slice d a
    · simp only [eG, Set.indicator_of_mem hv]; exact (hw v hv).1
    · simp only [eG, Set.indicator_of_notMem hv, abs_zero]; exact hε0
  have hmδ' : ∫ v, dG D c d a v ∂pm = 0 := by
    rw [hpm, integral_gMeas d hβ]
    have : (slice d a).indicator (dG D c d a) = (slice d a).indicator
        (fun v => lA D c a v - d.lam0 a) := by
      unfold dG; rw [Set.indicator_indicator, Set.inter_self]
    rw [this, integral_indicator ms, hmδ, mul_zero]
  have hmε' : ∫ v, eG D c d a v ∂pm = 0 := by
    rw [hpm, integral_gMeas d hβ]
    have : (slice d a).indicator (eG D c d a) = (slice d a).indicator
        (fun v => sA D c a v / d.S0 a - 1) := by
      unfold eG; rw [Set.indicator_indicator, Set.inter_self]
    rw [this, integral_indicator ms, hmε, mul_zero]
  have h := chi_six pm n (measurable_dG D c d a) (measurable_eG D c d a) ha2.le hε₀ hwε hwδ hmδ' hmε'
  rw [← chiK_eq_gMeas D c d hβ] at h
  refine h.trans (le_of_eq ?_)
  have hY : ∀ k : ℕ, k ≠ 0 → momN pm k (fun v => √a2 * dG D c d a v) = √a2 * momN pm k (dG D c d a) :=
    fun k hk => by rw [momN_const_mul pm hk, abs_of_pos hsa]
  have hsq : √a2 ^ 2 = a2 := Real.sq_sqrt ha2.le
  have hB : ∀ k : ℕ, k ≠ 0 → bigT pm k n a2 κ δ₀ (dG D c d a) (eG D c d a) =
      tK κ n L (momN pm k (eG D c d a)) (momN pm k (fun v => √a2 * dG D c d a v)) := fun k hk => by
    rw [hY k hk]
    unfold bigT tK
    have k1 : a2 * δ₀ = L * √a2 := by
      rw [hδ₀, div_eq_mul_inv]
      calc a2 * (L * (√a2)⁻¹) = L * (√a2 * √a2 * (√a2)⁻¹) := by
            rw [Real.mul_self_sqrt ha2.le]; ring
        _ = L * √a2 := by field_simp
    have k2 : a2 * momN pm k (dG D c d a) ^ 2 = (√a2 * momN pm k (dG D c d a)) ^ 2 := by
      rw [mul_pow, hsq]
    rw [k2, show a2 * δ₀ * momN pm k (dG D c d a) * momN pm k (eG D c d a) =
      (a2 * δ₀) * momN pm k (dG D c d a) * momN pm k (eG D c d a) by ring, k1]
    ring
  have e1 : ∫ v, eG D c d a v ^ 2 ∂pm = momN pm 2 (eG D c d a) ^ 2 := by
    rw [momN_pow pm two_ne_zero]; simp_rw [sq_abs]
  have e2 : ∫ v, dG D c d a v ^ 2 ∂pm = momN pm 2 (dG D c d a) ^ 2 := by
    rw [momN_pow pm two_ne_zero]; simp_rw [sq_abs]
  have e3 : a2 * δ₀ ^ 2 = L ^ 2 := by
    rw [hδ₀, div_pow, hsq]; field_simp
  rw [hB 2 two_ne_zero, hB 4 (by norm_num), hB 6 (by norm_num), e1, e2, e3, hY 2 two_ne_zero]
  unfold sixF
  rw [mul_pow, hsq]
  ring


/-! ## Conditional moments on the good slices -/

/-- **The good-conditional `k`-th absolute moment** of a field `F(a, v)` that vanishes off the
good slice: `(1 − β(a))^{−1} ∫ |F(a, v)|^k dν(v)` (the moment for the normalized good-set
measure, `condMom_eq`). -/
noncomputable def condMom (d : SplitData n) (F : Ix n → (Fin (n - 1) → ℝ) → ℝ) (k : ℕ)
    (a : Ix n) : ℝ :=
  (1 - removed (stdGauss (Fin (n - 1))) d.good a)⁻¹ * ∫ v, |F a v| ^ k ∂stdGauss (Fin (n - 1))

/-- The field `ε` as a function of `(a, v)`. -/
noncomputable def epsF (D : Design n) (c : Ret n) (d : SplitData n) :
    Ix n → (Fin (n - 1) → ℝ) → ℝ := fun a v => eG D c d a v

/-- The field `a_c δ = √(|c_A|²/S₀(a))·δ` as a function of `(a, v)`. -/
noncomputable def delF (D : Design n) (c : Ret n) (d : SplitData n) :
    Ix n → (Fin (n - 1) → ℝ) → ℝ := fun a v => √(normSq c.2.1.2 / d.S0 a) * dG D c d a v

lemma measurable_epsF (D : Design n) (c : Ret n) (d : SplitData n) :
    Measurable (Function.uncurry (epsF D c d)) := by
  have e : Function.uncurry (epsF D c d) =
      d.good.indicator (fun p : Ix n × (Fin (n - 1) → ℝ) => sA D c p.1 p.2 / d.S0 p.1 - 1) := by
    funext p
    simp only [Function.uncurry, epsF, eG, Set.indicator, slice]
    rfl
  rw [e]
  exact (((measurable_sA D c).div (d.mS0.comp measurable_fst)).sub_const 1).indicator d.mgood

lemma measurable_delF (D : Design n) (c : Ret n) (d : SplitData n) :
    Measurable (Function.uncurry (delF D c d)) := by
  have e : Function.uncurry (delF D c d) = fun p : Ix n × (Fin (n - 1) → ℝ) =>
      √(normSq c.2.1.2 / d.S0 p.1) *
        d.good.indicator (fun p : Ix n × (Fin (n - 1) → ℝ) => lA D c p.1 p.2 - d.lam0 p.1) p := by
    funext p
    simp only [Function.uncurry, delF, dG, Set.indicator, slice]
    rfl
  rw [e]
  exact ((measurable_const.div (d.mS0.comp measurable_fst)).sqrt).mul
    (((measurable_lA D c).sub (d.mlam0.comp measurable_fst)).indicator d.mgood)

lemma measurable_condMom (d : SplitData n) {F : Ix n → (Fin (n - 1) → ℝ) → ℝ}
    (hF : Measurable (Function.uncurry F)) (k : ℕ) : Measurable (condMom d F k) := by
  unfold condMom
  have h : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => |F p.1 p.2| ^ k) :=
    (hF.abs).pow_const k
  exact ((measurable_const.sub (measurable_removed _ d.mgood)).inv).mul
    (h.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin (n - 1)))).measurable

/-- On an index with `β(a) < 1`, for a field vanishing off the slice and `k ≥ 1`:
`condMom = E_{gMeas}|F|^k`. -/
lemma condMom_eq (d : SplitData n) {F : Ix n → (Fin (n - 1) → ℝ) → ℝ}
    (hvan : ∀ a v, v ∉ slice d a → F a v = 0) {a : Ix n}
    (hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1) {k : ℕ} (hk : k ≠ 0) :
    condMom d F k a = ∫ v, |F a v| ^ k ∂gMeas d a := by
  rw [integral_gMeas d hβ]
  unfold condMom
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  by_cases hv : v ∈ slice d a
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, hvan a v hv, abs_zero, zero_pow hk]

lemma momN_eq_condMom (d : SplitData n) {F : Ix n → (Fin (n - 1) → ℝ) → ℝ}
    (hvan : ∀ a v, v ∉ slice d a → F a v = 0) {a : Ix n}
    (hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1) {k : ℕ} (hk : k ≠ 0) :
    momN (gMeas d a) k (F a) = condMom d F k a ^ ((k : ℝ)⁻¹) := by
  rw [condMom_eq d hvan hβ hk]; rfl

lemma condMom_bounds (d : SplitData n) {F : Ix n → (Fin (n - 1) → ℝ) → ℝ}
    (hF : Measurable (Function.uncurry F))
    (hvan : ∀ a v, v ∉ slice d a → F a v = 0) {a : Ix n}
    (hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1) {K : ℝ} (hK : ∀ v, |F a v| ≤ K)
    {k : ℕ} (hk : k ≠ 0) : 0 ≤ condMom d F k a ∧ condMom d F k a ≤ K ^ k := by
  have hP := isProb_gMeas d hβ
  have mF : Measurable (F a) := hF.comp measurable_prodMk_left
  rw [condMom_eq d hvan hβ hk]
  refine ⟨integral_nonneg fun v => pow_nonneg (abs_nonneg _) _, ?_⟩
  have hi : Integrable (fun v => |F a v| ^ k) (gMeas d a) :=
    Integrable.of_bound (mF.abs.pow_const k).aestronglyMeasurable (K ^ k)
      (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hK v) k)
  calc ∫ v, |F a v| ^ k ∂gMeas d a ≤ ∫ _v, K ^ k ∂gMeas d a :=
        integral_mono hi (integrable_const _) fun v => pow_le_pow_left₀ (abs_nonneg _) (hK v) k
    _ = K ^ k := by simp

/-- Jensen: `(E|F|^k)² ≤ E|F|^{2k}` for the normalized good-set measure. -/
lemma condMom_sq_le (d : SplitData n) {F : Ix n → (Fin (n - 1) → ℝ) → ℝ}
    (hF : Measurable (Function.uncurry F))
    (hvan : ∀ a v, v ∉ slice d a → F a v = 0) {a : Ix n}
    (hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1) {K : ℝ} (hK : ∀ v, |F a v| ≤ K)
    {k : ℕ} (hk : k ≠ 0) : condMom d F k a ^ 2 ≤ condMom d F (2 * k) a := by
  have hP := isProb_gMeas d hβ
  have mF : Measurable (F a) := hF.comp measurable_prodMk_left
  rw [condMom_eq d hvan hβ hk, condMom_eq d hvan hβ (by omega)]
  have ib : ∀ j : ℕ, Integrable (fun v => |F a v| ^ j) (gMeas d a) := fun j =>
    Integrable.of_bound (mF.abs.pow_const j).aestronglyMeasurable (K ^ j)
      (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hK v) j)
  have h := BstLean.Part138.cs_sq (gMeas d a) (f := fun v => |F a v| ^ k) (g := fun _ => (1 : ℝ))
    (by simpa only [← pow_mul, mul_comm k 2] using ib (2 * k)) (integrable_const _)
    (by simpa using ib k)
  simp only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul] at h
  simpa only [← pow_mul, mul_comm k 2] using h

lemma rpow_inv_pow_two_mul {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : k ≠ 0) :
    (x ^ ((k : ℝ)⁻¹)) ^ (2 * k) = x ^ 2 := by
  rw [pow_mul', Real.rpow_inv_natCast_pow hx hk]


/-! ## Integration over the kept indices -/

lemma sixF_zero (κ n L ε₀ E : ℝ) : sixF κ n L ε₀ E 0 0 0 0 0 0 = 0 := by
  unfold sixF tK; ring

lemma tK_mono {κ n L x y x' y' : ℝ} (hκ : 0 ≤ κ) (hn : 0 ≤ n) (hL : 0 ≤ L) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hxx : x ≤ x') (hyy : y ≤ y') : tK κ n L x y ≤ tK κ n L x' y' := by
  have : 0 ≤ y' := hy.trans hyy
  unfold tK; gcongr

lemma sixF_mono {κ n L ε₀ E : ℝ} (hκ : 0 ≤ κ) (hn : 0 ≤ n) (hL : 0 ≤ L) (hε : 0 ≤ 1 + ε₀)
    (hE : 0 ≤ E) {x2 y2 x4 y4 x6 y6 M : ℝ} (h2 : 0 ≤ x2 ∧ x2 ≤ M) (g2 : 0 ≤ y2 ∧ y2 ≤ M)
    (h4 : 0 ≤ x4 ∧ x4 ≤ M) (g4 : 0 ≤ y4 ∧ y4 ≤ M) (h6 : 0 ≤ x6 ∧ x6 ≤ M) (g6 : 0 ≤ y6 ∧ y6 ≤ M) :
    0 ≤ sixF κ n L ε₀ E x2 y2 x4 y4 x6 y6 ∧
      sixF κ n L ε₀ E x2 y2 x4 y4 x6 y6 ≤ sixF κ n L ε₀ E M M M M M M := by
  have t2 := tK_nonneg hκ hn hL h2.1 g2.1
  have t4 := tK_nonneg hκ hn hL h4.1 g4.1
  have t6 := tK_nonneg hκ hn hL h6.1 g6.1
  have m2 := tK_mono hκ hn hL h2.1 g2.1 h2.2 g2.2
  have m4 := tK_mono hκ hn hL h4.1 g4.1 h4.2 g4.2
  have m6 := tK_mono hκ hn hL h6.1 g6.1 h6.2 g6.2
  constructor
  · unfold sixF
    have := h2.1; have := g2.1
    positivity
  · have hM : 0 ≤ M := h2.1.trans h2.2
    have tM := tK_nonneg hκ hn hL hM hM
    unfold sixF
    have := h2.1; have := g2.1
    gcongr
    all_goals first | exact h2.2 | exact g2.2 | assumption | positivity

/-- One field: `∫ (1_K · condMom_k^{1/k})^{2k} ≤ J` from `∫_K condMom_k² ≤ J`. -/
lemma field_int_sq (d : SplitData n) {K : Set (Ix n)} (mK : MeasurableSet K)
    (hK : ∀ a ∈ K, removed (stdGauss (Fin (n - 1))) d.good a < 1)
    {F : Ix n → (Fin (n - 1) → ℝ) → ℝ} (hF : Measurable (Function.uncurry F))
    (hvan : ∀ a v, v ∉ slice d a → F a v = 0) {k : ℕ} (hk : k ≠ 0) {J : ℝ}
    (hJ : ∫ a in K, condMom d F k a ^ 2 ∂muI n ≤ J) :
    ∫ a, (K.indicator (fun a => condMom d F k a ^ ((k : ℝ)⁻¹)) a) ^ (2 * k) ∂muI n ≤ J := by
  have e : (fun a => (K.indicator (fun a => condMom d F k a ^ ((k : ℝ)⁻¹)) a) ^ (2 * k)) =
      K.indicator (fun a => condMom d F k a ^ 2) := by
    funext a
    by_cases ha : a ∈ K
    · simp only [Set.indicator_of_mem ha]
      have h0 : 0 ≤ condMom d F k a := by
        unfold condMom
        exact mul_nonneg (inv_nonneg.mpr (by linarith [hK a ha]))
          (integral_nonneg fun v => pow_nonneg (abs_nonneg _) _)
      exact rpow_inv_pow_two_mul h0 hk
    · simp only [Set.indicator_of_notMem ha, zero_pow (by omega : 2 * k ≠ 0)]
  rw [e, integral_indicator mK]
  exact hJ

/-- One field: `∫ (1_K · condMom_k^{1/k})^{2k} ≤ J` from the joint moment `∫_K condMom_{2k} ≤ J`
(conditional Jensen on each slice). -/
lemma field_int (d : SplitData n) {K : Set (Ix n)} (mK : MeasurableSet K)
    (hK : ∀ a ∈ K, removed (stdGauss (Fin (n - 1))) d.good a < 1)
    {F : Ix n → (Fin (n - 1) → ℝ) → ℝ} (hF : Measurable (Function.uncurry F))
    (hvan : ∀ a v, v ∉ slice d a → F a v = 0) {Kb : ℝ} (hbd : ∀ a ∈ K, ∀ v, |F a v| ≤ Kb)
    {k : ℕ} (hk : k ≠ 0) {J : ℝ} (hJ : ∫ a in K, condMom d F (2 * k) a ∂muI n ≤ J) :
    ∫ a, (K.indicator (fun a => condMom d F k a ^ ((k : ℝ)⁻¹)) a) ^ (2 * k) ∂muI n ≤ J := by
  refine field_int_sq d mK hK hF hvan hk (le_trans ?_ hJ)
  have mc := measurable_condMom d hF
  refine setIntegral_mono_on ?_ ?_ mK fun a ha => condMom_sq_le d hF hvan (hK a ha) (hbd a ha) hk
  · refine Integrable.of_bound ((mc k).pow_const 2).aestronglyMeasurable ((Kb ^ k) ^ 2)
      (ae_restrict_of_forall_mem mK fun a ha => ?_)
    obtain ⟨h0, h1⟩ := condMom_bounds d hF hvan (hK a ha) (hbd a ha) hk
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ h0 h1 2
  · refine Integrable.of_bound (mc (2 * k)).aestronglyMeasurable (Kb ^ (2 * k))
      (ae_restrict_of_forall_mem mK fun a ha => ?_)
    obtain ⟨h0, h1⟩ := condMom_bounds d hF hvan (hK a ha) (hbd a ha) (by omega : 2 * k ≠ 0)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1

lemma field_bound (d : SplitData n) {K : Set (Ix n)}
    (hK : ∀ a ∈ K, removed (stdGauss (Fin (n - 1))) d.good a < 1)
    {F : Ix n → (Fin (n - 1) → ℝ) → ℝ} (hF : Measurable (Function.uncurry F))
    (hvan : ∀ a v, v ∉ slice d a → F a v = 0) {Kb : ℝ} (hKb : 0 ≤ Kb)
    (hbd : ∀ a ∈ K, ∀ v, |F a v| ≤ Kb) {k : ℕ} (hk : k ≠ 0) (a : Ix n) :
    0 ≤ K.indicator (fun a => condMom d F k a ^ ((k : ℝ)⁻¹)) a ∧
      K.indicator (fun a => condMom d F k a ^ ((k : ℝ)⁻¹)) a ≤ Kb := by
  by_cases ha : a ∈ K
  · simp only [Set.indicator_of_mem ha]
    obtain ⟨h0, h1⟩ := condMom_bounds d hF hvan (hK a ha) (hbd a ha) hk
    refine ⟨Real.rpow_nonneg h0 _, ?_⟩
    calc condMom d F k a ^ ((k : ℝ)⁻¹) ≤ (Kb ^ k) ^ ((k : ℝ)⁻¹) :=
          Real.rpow_le_rpow h0 h1 (by positivity)
      _ = Kb := Real.pow_rpow_inv_natCast hKb hk
  · simp only [Set.indicator_of_notMem ha]; exact ⟨le_rfl, hKb⟩


/-- **Proposition FL, chi-square part, from the joint moments (`FLUCT_chi_hyp` with the price
`𝒞`).** Hypotheses, for every kept index `a`: `S₀(a) ≥ s_low > 0`; on the good slice,
`|S(x)/S₀(a) − 1| ≤ ε₀ < 1`, `|λ(x) − λ₀(a)| ≤ δ₀`, `a_c²(λ(x) − λ₀(a))² ≤ L²`; the references are
the good-set means. Moments (the paper's `A`, `D`, `e_k`, `d_k`, for the joint distribution of
the latitude index and the normalized good sets, restricted to the kept indices):
`∫_K (E_a ε²)² ≤ A²`, `∫_K (E_a (a_cδ)²)² ≤ D²`, `∫_K E_a ε⁸ ≤ e₄⁸`, `∫_K E_a (a_cδ)⁸ ≤ d₄⁸`,
`∫_K E_a ε¹² ≤ e₆¹²`, `∫_K E_a (a_cδ)¹² ≤ d₆¹²`. With `B ≥ E β`, `Dd ≥ E_K H²(Q_a, Q̄_a)` and
`√(2(1 + 1/η)B) + √𝒞 + √Dd ≤ h_fl`, THEN `FLUCT_chi_hyp D c d ε₀ δ₀ s_low h_fl`. -/
theorem fluct_of_moments (D : Design n) (c : Ret n) (d : SplitData n)
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
    (hsum : √(2 * (1 + d.eta⁻¹) * B) + √(priceC (1 - ε₀ ^ 2)⁻¹ n L ε₀
        (exp ((1 - ε₀ ^ 2)⁻¹ * (n * ε₀ ^ 2 / 2 + L ^ 2 * (1 + ε₀)))) A Dm e4 d4 e6 d6) + √Dd ≤
      hfl) :
    FLUCT_chi_hyp D c d ε₀ δ₀ slow hfl := by
  set ν := stdGauss (Fin (n - 1))
  set K := keptIx D c d with hKd
  have mK : MeasurableSet K :=
    measurableSet_keptSet ν d.mgood (measurableSet_bulkIx D c) d.eta
  have hKβ : ∀ a ∈ K, removed ν d.good a < 1 := fun a ha => lt_of_le_of_lt ha.2 d.eta_lt
  set κ := (1 - ε₀ ^ 2)⁻¹ with hκ
  have hκ0 : 0 ≤ κ := inv_nonneg.mpr (by nlinarith)
  set E := exp ((1 - ε₀ ^ 2)⁻¹ * (n * ε₀ ^ 2 / 2 + L ^ 2 * (1 + ε₀))) with hE
  refine ⟨hε0, hε₀, hδ0, hslow, fun a ha => ⟨(hwin a ha).1, fun v hv =>
    ⟨((hwin a ha).2 v hv).1, ((hwin a ha).2 v hv).2.1⟩⟩, B,
    priceC κ n L ε₀ E A Dm e4 d4 e6 d6, Dd, hB, ?_, hD, hsum⟩
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

end BstLean.Part162

open BstLean.Part162 in
#print axioms chiK_le_sixF
open BstLean.Part162 in
#print axioms fluct_of_moments
