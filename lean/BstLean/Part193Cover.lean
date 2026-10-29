import BstLean.Part193Interval
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-! Part 193: finite cell coverage and checked local scalar bounds.
Cells are proof sets. They need no disjointness or measurable-set premise.
The finite cover contributes no event-complement charge. -/
namespace BstLean.Part193
open MeasureTheory

/-- The selected cells cover every point of the stated domain. -/
structure FiniteCover (α ι : Type*) (domain : Set α) where
  indices : Finset ι
  cell : ι → Set α
  covers : ∀ x ∈ domain, ∃ i ∈ indices, x ∈ cell i

/-- Each selected cell has a proved enclosure of the exact scalar function. -/
structure CheckedBounds {α ι : Type*} {domain : Set α}
    (C : FiniteCover α ι domain) (f : α → ℝ) where
  bound : ι → Interval
  encloses : ∀ i ∈ C.indices, ∀ x ∈ domain, x ∈ C.cell i → (bound i).Mem (f x)

theorem finite_cover_uniform_bound {α ι : Type*} {domain : Set α}
    (C : FiniteCover α ι domain) {f : α → ℝ} (B : CheckedBounds C f)
    {L U : ℝ} (hl : ∀ i ∈ C.indices, L ≤ (B.bound i).lo)
    (hu : ∀ i ∈ C.indices, (B.bound i).hi ≤ U) :
    ∀ x ∈ domain, L ≤ f x ∧ f x ≤ U := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := C.covers x hx
  have h := B.encloses i hi x hx hxi
  exact ⟨(hl i hi).trans h.1, h.2.trans (hu i hi)⟩

theorem finite_cover_uniform_upper {α ι : Type*} {domain : Set α}
    (C : FiniteCover α ι domain) {f : α → ℝ} (B : CheckedBounds C f)
    {U : ℝ} (hu : ∀ i ∈ C.indices, (B.bound i).hi ≤ U) :
    ∀ x ∈ domain, f x ≤ U := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := C.covers x hx
  exact (B.encloses i hi x hx hxi).2.trans (hu i hi)

/-- Local scalar guards transfer through the same cover. -/
theorem finite_cover_property {α ι : Type*} {domain : Set α}
    (C : FiniteCover α ι domain) {P : α → Prop}
    (h : ∀ i ∈ C.indices, ∀ x ∈ domain, x ∈ C.cell i → P x) :
    ∀ x ∈ domain, P x := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := C.covers x hx
  exact h i hi x hx hxi

/-- The failure set is contained in the complement of the retained domain.
There is no sum of charges over the cells. -/
theorem finite_cover_failure_subset {α ι : Type*} {domain : Set α}
    (C : FiniteCover α ι domain) {f : α → ℝ} (B : CheckedBounds C f)
    {U : ℝ} (hu : ∀ i ∈ C.indices, (B.bound i).hi ≤ U) :
    {x | U < f x} ⊆ domainᶜ := by
  intro x hx hxd
  exact (not_lt_of_ge (finite_cover_uniform_upper C B hu x hxd)) hx

theorem finite_cover_failure_measure_le {α ι : Type*} [MeasurableSpace α]
    {domain : Set α} (C : FiniteCover α ι domain) {f : α → ℝ}
    (B : CheckedBounds C f) (μ : MeasureTheory.Measure α) {U : ℝ}
    (hu : ∀ i ∈ C.indices, (B.bound i).hi ≤ U) :
    μ {x | U < f x} ≤ μ domainᶜ :=
  measure_mono (finite_cover_failure_subset C B hu)

/-- An empty selected family covers only an empty domain. -/
theorem empty_cover_domain {α ι : Type*} {domain : Set α}
    (C : FiniteCover α ι domain) (h : C.indices = ∅) : domain = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i, hi, _⟩ := C.covers x hx
  simp [h] at hi

/-- Adjacent closed cells cover a chain, including shared endpoints.
The statement keeps the cell order as a separate checked premise. -/
theorem chain_coverage (e : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    (hstep : ∀ j < N, e j ≤ e (j + 1)) {x : ℝ}
    (hx : e 0 ≤ x ∧ x ≤ e N) :
    ∃ j ∈ Finset.range N, e j ≤ x ∧ x ≤ e (j + 1) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h : x ≤ e N
    · by_cases hn : 0 < N
      · obtain ⟨j, hj, hcell⟩ := ih hn (fun j hj => hstep j (by omega)) ⟨hx.1, h⟩
        exact ⟨j, Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega), hcell⟩
      · have hn0 : N = 0 := by omega
        subst N
        exact ⟨0, by simp, hx⟩
    · exact ⟨N, Finset.mem_range.mpr (by omega), ⟨(lt_of_not_ge h).le, hx.2⟩⟩

noncomputable def chainCover (e : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hstep : ∀ j < N, e j ≤ e (j + 1)) :
    FiniteCover ℝ ℕ (Set.Icc (e 0) (e N)) where
  indices := Finset.range N
  cell := fun j => Set.Icc (e j) (e (j + 1))
  covers := fun _ hx => chain_coverage e hN hstep hx

/-- Every positive number of affine cells covers the full closed interval. -/
theorem affine_chain_coverage {a b x : ℝ} (hab : a ≤ b) {N : ℕ} (hN : 0 < N)
    (hx : a ≤ x ∧ x ≤ b) :
    ∃ j ∈ Finset.range N,
      a + (b - a) * (j : ℝ) / (N : ℝ) ≤ x ∧
      x ≤ a + (b - a) * ((j + 1 : ℕ) : ℝ) / (N : ℝ) := by
  let e : ℕ → ℝ := fun j => a + (b - a) * (j : ℝ) / (N : ℝ)
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have he0 : e 0 = a := by simp [e]
  have heN : e N = b := by simp [e, ne_of_gt hn]
  have hstep : ∀ j < N, e j ≤ e (j + 1) := by
    intro j _
    dsimp [e]
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ hn.le
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
    exact_mod_cast Nat.le_succ j
  exact chain_coverage e hN hstep (by simpa [he0, heN] using hx)

noncomputable def affineCover (a b : ℝ) (hab : a ≤ b) (N : ℕ) (hN : 0 < N) :
    FiniteCover ℝ ℕ (Set.Icc a b) where
  indices := Finset.range N
  cell := fun j => Set.Icc (a + (b - a) * (j : ℝ) / (N : ℝ))
    (a + (b - a) * ((j + 1 : ℕ) : ℝ) / (N : ℝ))
  covers := fun _ hx => affine_chain_coverage hab hN hx

/-- A finite dimension row table covers its stated closed dimension interval. -/
noncomputable def dimensionCover (lo hi : ℕ) : FiniteCover ℕ ℕ (Set.Icc lo hi) where
  indices := Finset.Icc lo hi
  cell := fun n => {n}
  covers := fun n hn => ⟨n, Finset.mem_Icc.mpr hn, rfl⟩

/-- Overlapping cells also cover a domain when they contain a checked chain. -/
noncomputable def enlargedChainCover (e : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hstep : ∀ j < N, e j ≤ e (j + 1)) (cell : ℕ → Set ℝ)
    (hcontains : ∀ j < N, Set.Icc (e j) (e (j + 1)) ⊆ cell j) :
    FiniteCover ℝ ℕ (Set.Icc (e 0) (e N)) where
  indices := Finset.range N
  cell := cell
  covers := by
    intro x hx
    obtain ⟨j, hj, hcell⟩ := chain_coverage e hN hstep hx
    exact ⟨j, hj, hcontains j (Finset.mem_range.mp hj) hcell⟩

/-- Products of checked covers supply the two-dimensional cell cover. -/
noncomputable def productCover {α β ι κ : Type*} {S : Set α} {T : Set β}
    (C : FiniteCover α ι S) (D : FiniteCover β κ T) :
    FiniteCover (α × β) (ι × κ) (S ×ˢ T) where
  indices := C.indices.product D.indices
  cell := fun i => C.cell i.1 ×ˢ D.cell i.2
  covers := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := C.covers x.1 hx.1
    obtain ⟨j, hj, hxj⟩ := D.covers x.2 hx.2
    exact ⟨(i, j), Finset.mem_product.mpr ⟨hi, hj⟩, hxi, hxj⟩

end BstLean.Part193
