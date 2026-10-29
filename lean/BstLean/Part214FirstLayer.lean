import BstLean.Part214Charge
import BstLean.Part214Diagonal
import BstLean.Part214Norm
import BstLean.Part214ScaledDiagonal

/-! The first-layer event uses one norm payment, four variance payments and one mean payment. -/
namespace BstLean.Part214
open MeasureTheory Real Set
open BstLean.Part29 BstLean.Part130

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The six inequalities have the same parameterized thresholds as P10e E1. -/
def firstLayerEvent (ω H : Ω → ℝ) (Y : Fin 4 → Ω → ℝ)
    (εω EH ph : ℝ) (A ε : Fin 4 → ℝ) : Set Ω :=
  {x | |ω x - 1| ≤ εω ∧ (∀ i, Y i x ≤ (1 + ε i) * A i) ∧ H x ≤ EH / ph}

theorem firstLayerEvent_measurable {ω H : Ω → ℝ} {Y : Fin 4 → Ω → ℝ}
    (mω : Measurable ω) (mH : Measurable H) (mY : ∀ i, Measurable (Y i))
    (εω EH ph : ℝ) (A ε : Fin 4 → ℝ) :
    MeasurableSet (firstLayerEvent ω H Y εω EH ph A ε) := by
  have hY : MeasurableSet {x | ∀ i, Y i x ≤ (1 + ε i) * A i} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (mY i) measurable_const
  exact (measurableSet_le ((mω.sub measurable_const).abs) measurable_const).inter
    (hY.inter (measurableSet_le mH measurable_const))

/-- Nonnegative Markov at the exact threshold `EH/ph`. -/
theorem nonnegative_mean_charge {H : Ω → ℝ} (hH : ∀ x, 0 ≤ H x)
    (iH : Integrable H P) {EH ph : ℝ} (hEH : 0 < EH) (hph : 0 < ph)
    (hmean : (∫ x, H x ∂P) ≤ EH) :
    P.real {x | EH / ph < H x} ≤ ph := by
  have hr : 0 < EH / ph := div_pos hEH hph
  have hs : {x | EH / ph < H x} ⊆ {x | EH / ph ≤ H x} := by
    intro x hx
    exact (show EH / ph < H x from hx).le
  have h := (mul_le_mul_of_nonneg_left (measureReal_mono hs) hr.le).trans
    ((mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hH) iH (EH / ph)).trans hmean)
  have he : EH = EH / ph * ph := by field_simp
  exact le_of_mul_le_mul_left (h.trans_eq he) hr

/-- The E1 union charge follows from the supplied first-layer moments, with no independence premise. -/
theorem firstLayerEvent_charge {ω H : Ω → ℝ} {Y : Fin 4 → Ω → ℝ}
    {εω EH ph dω : ℝ} {A ε c V : Fin 4 → ℝ}
    (hA : ∀ i, 0 < A i) (hε : ∀ i, 0 < ε i) (hEH : 0 < EH) (hph : 0 < ph)
    (hω : P.real {x | εω < |ω x - 1|} ≤ dω)
    (hH : ∀ x, 0 ≤ H x) (iH : Integrable H P) (hmeanH : (∫ x, H x ∂P) ≤ EH)
    (hi : ∀ i, Integrable (fun x => (Y i x - c i) ^ 2) P)
    (hc : ∀ i, c i ≤ A i) (hv : ∀ i, (∫ x, (Y i x - c i) ^ 2 ∂P) ≤ V i) :
    P.real (firstLayerEvent ω H Y εω EH ph A ε)ᶜ ≤
      dω + (∑ i, V i / (ε i * A i) ^ 2) + ph := by
  have hy : ∀ i, P.real {x | (1 + ε i) * A i < Y i x} ≤ V i / (ε i * A i) ^ 2 := by
    intro i
    have hr : A i < (1 + ε i) * A i := by nlinarith [mul_pos (hε i) (hA i)]
    have he : (1 + ε i) * A i - A i = ε i * A i := by ring
    simpa only [he] using upper_tail_of_mean_bound (hi i) (hv i) (hc i) hr
  have hs : (firstLayerEvent ω H Y εω EH ph A ε)ᶜ ⊆
      ({x | εω < |ω x - 1|} ∪ ⋃ i, {x | (1 + ε i) * A i < Y i x}) ∪
        {x | EH / ph < H x} := by
    classical
    intro x hx
    by_cases ho : |ω x - 1| ≤ εω
    · by_cases hy : ∀ i, Y i x ≤ (1 + ε i) * A i
      · exact Or.inr (lt_of_not_ge fun hh => hx ⟨ho, hy, hh⟩)
      · obtain ⟨i, hi⟩ := not_forall.mp hy
        exact Or.inl (Or.inr (mem_iUnion.mpr ⟨i, lt_of_not_ge hi⟩))
    · exact Or.inl (Or.inl (lt_of_not_ge ho))
  have hb := (measureReal_mono (μ := P) hs).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) (le_refl _)))
  exact hb.trans (add_le_add
    (add_le_add hω ((measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun i _ => hy i)))
    (nonnegative_mean_charge P hH iH hEH hph hmeanH))

end

/-- The diagonal term of E1 has a concrete Gaussian supply. -/
theorem diagonal_upper_charge {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    (gaussMat m N 1).real {M | (1 + ε) * ((m : ℝ) * N * (N + 2)) < diagonalSum N m M} ≤
      (8 * (m : ℝ) * N * (N + 2) * (N + 3)) /
        (ε * ((m : ℝ) * N * (N + 2))) ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : (m : ℝ) * N * (N + 2) < (1 + ε) * ((m : ℝ) * N * (N + 2)) := by
    nlinarith [mul_pos hε (show 0 < (m : ℝ) * N * (N + 2) by positivity)]
  have he : (1 + ε) * ((m : ℝ) * N * (N + 2)) - (m : ℝ) * N * (N + 2) =
      ε * ((m : ℝ) * N * (N + 2)) := by ring
  simpa only [he] using upper_tail_of_mean_bound (diagonal_variance hN).1
    (diagonal_variance hN).2.le (le_refl ((m : ℝ) * N * (N + 2))) hr

/-- The diagonal variance payment also holds directly under the He-scaled distribution. -/
theorem paperDiagonal_upper_charge {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    (gaussMat m N (2 / (N : ℝ))).real
      {M | (1 + ε) * ((m : ℝ) * N * (N + 2)) < paperDiagonal N m M} ≤
      (8 * (m : ℝ) * N * (N + 2) * (N + 3)) /
        (ε * ((m : ℝ) * N * (N + 2))) ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : (m : ℝ) * N * (N + 2) < (1 + ε) * ((m : ℝ) * N * (N + 2)) := by
    nlinarith [mul_pos hε (show 0 < (m : ℝ) * N * (N + 2) by positivity)]
  have he : (1 + ε) * ((m : ℝ) * N * (N + 2)) - (m : ℝ) * N * (N + 2) =
      ε * ((m : ℝ) * N * (N + 2)) := by ring
  have h := paperDiagonal_moments (m := m) hN
  simpa only [he] using upper_tail_of_mean_bound h.2.2.1 h.2.2.2.le
    (le_refl ((m : ℝ) * N * (N + 2))) hr

/-- The actual first-layer E1 norm charge is supplied; the other moments remain explicit. -/
theorem firstLayerEvent_world_charge {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    {H : Matrix (Fin m) (Fin N) ℝ → ℝ}
    {Y : Fin 4 → Matrix (Fin m) (Fin N) ℝ → ℝ}
    (mH : Measurable H) (mY : ∀ i, Measurable (Y i))
    {εω EH ph : ℝ} {A ε c V : Fin 4 → ℝ}
    (hεω : 0 < εω) (hεω1 : εω < 1)
    (hA : ∀ i, 0 < A i) (hε : ∀ i, 0 < ε i) (hEH : 0 < EH) (hph : 0 < ph)
    (hH : ∀ x, 0 ≤ H x) (iH : Integrable H (gaussMat m N (2 / (N : ℝ))))
    (hmeanH : (∫ x, H x ∂gaussMat m N (2 / (N : ℝ))) ≤ EH)
    (hi : ∀ i, Integrable (fun x => (Y i x - c i) ^ 2) (gaussMat m N (2 / (N : ℝ))))
    (hc : ∀ i, c i ≤ A i)
    (hv : ∀ i, (∫ x, (Y i x - c i) ^ 2 ∂gaussMat m N (2 / (N : ℝ))) ≤ V i) :
    MeasurableSet (firstLayerEvent firstOmega H Y εω EH ph A ε) ∧
    (gaussMat m N (2 / (N : ℝ))).real (firstLayerEvent firstOmega H Y εω EH ph A ε)ᶜ ≤
      (exp (-((m : ℝ) * N) / 2 * (εω - log (1 + εω))) +
        exp (-((m : ℝ) * N) / 2 * (-εω - log (1 - εω)))) +
        (∑ i, V i / (ε i * A i) ^ 2) + ph := by
  exact ⟨firstLayerEvent_measurable measurable_firstOmega mH mY _ _ _ _ _,
    firstLayerEvent_charge _ hA hε hEH hph (firstOmega_charge hN hm hεω hεω1)
      hH iH hmeanH hi hc hv⟩

end BstLean.Part214
#print axioms BstLean.Part214.firstLayerEvent_charge
#print axioms BstLean.Part214.diagonal_upper_charge
#print axioms BstLean.Part214.paperDiagonal_upper_charge
#print axioms BstLean.Part214.firstLayerEvent_world_charge
