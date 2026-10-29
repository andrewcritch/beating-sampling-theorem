import BstLean.Part162Good

/-! The FL comparison integral, with its actual conditional moments and
integrability exposed before the final root-price comparison. -/
namespace BstLean.BlueprintLow
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162
variable {n : ℕ}

theorem conditional_chi_integral (D : Design n) (c : Ret n) (d : SplitData n)
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
    (Id6 : ∫ a in keptIx D c d, condMom d (delF D c d) 12 a ∂muI n ≤ d6 ^ 12)
    : IntegrableOn (chiK D c d) (keptIx D c d) (muI n) ∧
      (∫ a in keptIx D c d, chiK D c d a ∂muI n) ≤
        priceC (1 - ε₀ ^ 2)⁻¹ n L ε₀
          (exp ((1 - ε₀ ^ 2)⁻¹ * (n * ε₀ ^ 2 / 2 + L ^ 2 * (1 + ε₀))))
          A Dm e4 d4 e6 d6 := by
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
  refine ⟨iC, ?_⟩
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


end BstLean.BlueprintLow
