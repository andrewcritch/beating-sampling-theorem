import BstLean.Part199Events

/-! Part 199: common good pairs, row defects, and exceptional pair masses. -/
namespace BstLean.Part199
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part160 BstLean.Part182

variable {n : ℕ}

def pairFailure (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (w : Window) (lam : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | (((c, τ), (A₁, A₂)), p) ∈ badSet n w.t w.z w.pair lam}

def commonGood (c : Fin n → ℝ) (w : Window)
    (B : Set ((Fin n → ℝ) × (Fin n → ℝ))) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  GammaS c w.t w.z w.pair \ (B ∪ Prod.swap ⁻¹' B)

theorem measurableSet_pairFailure (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (w : Window) (lam : ℝ) : MeasurableSet (pairFailure A₁ A₂ c τ w lam) :=
  measurable_prodMk_left (measurableSet_badSet w.t w.z w.pair lam)

theorem measurableSet_commonGood (c : Fin n → ℝ) (w : Window)
    {B : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hB : MeasurableSet B) :
    MeasurableSet (commonGood c w B) :=
  (measurableSet_GammaS c w.t w.z w.pair).diff (hB.union (measurable_swap hB))

theorem commonGood_swap (c : Fin n → ℝ) (w : Window)
    (B : Set ((Fin n → ℝ) × (Fin n → ℝ))) (a b : Fin n → ℝ)
    (h : (a, b) ∈ commonGood c w B) : (b, a) ∈ commonGood c w B := by
  refine ⟨gammaS_swap h.1, ?_⟩
  rintro (h' | h')
  · exact h.2 (Or.inr h')
  · exact h.2 (Or.inl h')

/-- Removing both orientations doubles the one pair-mass bound. -/
theorem commonGood_exception (hn : 0 < n) (c : Fin n → ℝ) (w : Window)
    {B : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hB : MeasurableSet B)
    {b : ℝ} (hb : ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real B ≤ b) :
    ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real
      ((commonGood c w B)ᶜ ∩ OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z) ≤
      2 * exp (-w.pair ^ 2 / 2) + 2 * b := by
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  let μ := (stdGauss (Fin n)).prod (stdGauss (Fin n))
  have hs : μ.real (Prod.swap ⁻¹' B) = μ.real B := by
    rw [Measure.real, Measure.real,
      (Measure.measurePreserving_swap (μ := stdGauss (Fin n))
        (ν := stdGauss (Fin n))).measure_preimage hB.nullMeasurableSet]
  have hsub : (commonGood c w B)ᶜ ∩ OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z ⊆
      ((OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z) \ GammaS c w.t w.z w.pair) ∪
      B ∪ Prod.swap ⁻¹' B := by
    rintro p ⟨hno, hp⟩
    by_cases hΓ : p ∈ GammaS c w.t w.z w.pair
    · have hbad : p ∈ B ∪ Prod.swap ⁻¹' B := by
        by_contra hbad
        exact hno ⟨hΓ, hbad⟩
      rcases hbad with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · exact Or.inl (Or.inl ⟨hp, hΓ⟩)
  have hout := pairs_out_gamma hn c w.z_nonneg w.pair_nonneg (t0 := w.t)
  calc μ.real ((commonGood c w B)ᶜ ∩ OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z)
      ≤ μ.real (((OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z) \
          GammaS c w.t w.z w.pair) ∪ B ∪ Prod.swap ⁻¹' B) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real ((OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z) \ GammaS c w.t w.z w.pair) +
        μ.real B + μ.real (Prod.swap ⁻¹' B) :=
      (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
    _ ≤ 2 * exp (-w.pair ^ 2 / 2) + 2 * b := by rw [hs]; linarith

/-- The augmented core pair set makes the row defect zero outside the core.
On two core inputs its membership is exactly the core pair condition. -/
def coreKernelSet (c : Fin n → ℝ) (w : Window) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  GammaS c w.t w.z w.pair ∪ (OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z)ᶜ

theorem measurableSet_coreKernelSet (c : Fin n → ℝ) (w : Window) :
    MeasurableSet (coreKernelSet c w) :=
  (measurableSet_GammaS c w.t w.z w.pair).union
    ((measurableSet_OmegaS c w.t w.z).prod (measurableSet_OmegaS c w.t w.z)).compl

theorem coreKernelSet_swap (c : Fin n → ℝ) (w : Window) (a b : Fin n → ℝ)
    (h : (a, b) ∈ coreKernelSet c w) : (b, a) ∈ coreKernelSet c w := by
  rcases h with h | h
  · exact Or.inl (gammaS_swap h)
  · exact Or.inr (fun h' => h ⟨h'.2, h'.1⟩)

theorem coreKernelSet_row (hn : 0 < n) (c : Fin n → ℝ) (w : Window) (a : Fin n → ℝ) :
    (stdGauss (Fin n)).real {b | b ∈ OmegaS c w.t w.z ∧ (a, b) ∉ coreKernelSet c w} ≤
      2 * exp (-w.pair ^ 2 / 2) := by
  by_cases ha : a ∈ OmegaS c w.t w.z
  · refine le_trans (measureReal_mono (fun b hb => ?_) (measure_ne_top _ _))
      (gamma_row_le hn c w.z_nonneg w.pair_nonneg ha)
    exact ⟨hb.1, fun h => hb.2 (Or.inl h)⟩
  · have he : {b | b ∈ OmegaS c w.t w.z ∧ (a, b) ∉ coreKernelSet c w} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro b hb
      exact hb.2 (Or.inr (fun hp => ha hp.1))
    rw [he, measureReal_empty]
    positivity

theorem commonGood_wide_pair
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (w₀ w₁ : Window) (lam₀ lam₁ : ℝ) {a b : Fin n → ℝ}
    (h : (a, b) ∈ commonGood c w₀
      (pairFailure A₁ A₂ c τ w₀ lam₀ ∪ pairFailure A₁ A₂ c τ w₁ lam₁)) :
    opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤ (n : ℝ) * lam₀ := by
  apply not_lt.mp
  intro hbad
  exact h.2 (Or.inl (Or.inl ⟨h.1, hbad⟩))

theorem commonGood_core_pair
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (w₀ w₁ : Window) (lam₀ lam₁ : ℝ) {a b : Fin n → ℝ}
    (h : (a, b) ∈ commonGood c w₀
      (pairFailure A₁ A₂ c τ w₀ lam₀ ∪ pairFailure A₁ A₂ c τ w₁ lam₁))
    (ha : a ∈ OmegaS c w₁.t w₁.z) (hb : b ∈ OmegaS c w₁.t w₁.z) :
    opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤
      kern (coreKernelSet c w₁) ((n : ℝ) * lam₁) ((n : ℝ) * lam₀) a b := by
  by_cases hΓ : (a, b) ∈ GammaS c w₁.t w₁.z w₁.pair
  · rw [kern_of_mem (Or.inl hΓ : (a, b) ∈ coreKernelSet c w₁)]
    apply not_lt.mp
    intro hbad
    exact h.2 (Or.inl (Or.inr ⟨hΓ, hbad⟩))
  · have hno : (a, b) ∉ coreKernelSet c w₁ := by
      rintro (hp | hp)
      · exact hΓ hp
      · exact hp ⟨ha, hb⟩
    rw [kern_of_notMem hno]
    exact commonGood_wide_pair A₁ A₂ c τ w₀ w₁ lam₀ lam₁ h

end BstLean.Part199
