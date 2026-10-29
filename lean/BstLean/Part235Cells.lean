import BstLean.Part235Geometry
import BstLean.Part199TI

/-! Part 235: sixty theta cells and twelve overlap cells, with closed endpoints. -/
namespace BstLean.Part235
open BstLean.Part193 BstLean.Part199

noncomputable def thetaCover (a b : ℝ) (h : a ≤ b) :
    FiniteCover ℝ ℕ (Set.Icc a b) := affineCover a b h 60 (by norm_num)

noncomputable def overlapCover (lo hi : ℝ) (h : lo ≤ hi) :
    FiniteCover ℝ ℕ (Set.Icc lo hi) := affineCover lo hi h 12 (by norm_num)

noncomputable def overlapLo (lo hi : ℝ) (j : ℕ) : ℝ :=
  lo + (hi - lo) * (j : ℝ) / 12

noncomputable def overlapHi (lo hi : ℝ) (j : ℕ) : ℝ :=
  lo + (hi - lo) * ((j + 1 : ℕ) : ℝ) / 12

theorem overlapCover_cell {lo hi : ℝ} (h : lo ≤ hi) (j : ℕ) :
    (overlapCover lo hi h).cell j = Set.Icc (overlapLo lo hi j) (overlapHi lo hi j) := rfl

/-- The twelve overlap cells include both endpoints and every shared boundary. -/
theorem overlap_cell_contains {lo hi c : ℝ} (h : lo ≤ hi) (hc : c ∈ Set.Icc lo hi) :
    ∃ j < 12, overlapLo lo hi j ≤ c ∧ c ≤ overlapHi lo hi j := by
  obtain ⟨j, hj, hcell⟩ := (overlapCover lo hi h).covers c hc
  exact ⟨j, Finset.mem_range.mp hj, hcell⟩

/-- Each actual pair enters a deterministic overlap cell. No weight event is selected here. -/
theorem pair_cell_contains {n : ℕ} (hn : 0 < n) {c : Fin n → ℝ} {τ lo hi : ℝ}
    (hτ : 0 < τ) (w : Window) (hlohi : lo ≤ hi)
    (G : OverlapGuard n (BstLean.Part150.thetaC c τ) w lo hi)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ BstLean.Part182.GammaS c w.t w.z w.pair) :
    ∃ j < 12,
      overlapLo lo hi j ≤ dotProduct (BstLean.Part130.sphPt (c + τ • p.1))
        (BstLean.Part130.sphPt (c + τ • p.2)) ∧
      dotProduct (BstLean.Part130.sphPt (c + τ • p.1))
        (BstLean.Part130.sphPt (c + τ • p.2)) ≤ overlapHi lo hi j :=
  overlap_cell_contains hlohi (overlap_of_guard hn hτ w G hp)

/-- Local fixed-pair hypotheses supply a global TI hypothesis without a cell union charge.
The paper-sharp TI source can enter here as an explicit hypothesis. -/
theorem TI_of_twelve_cells {n : ℕ} {lo hi lam δ : ℝ} (h : lo ≤ hi)
    (hlocal : ∀ j < 12,
      BstLean.Part182.TI_hyp n (overlapLo lo hi j) (overlapHi lo hi j) lam δ) :
    BstLean.Part182.TI_hyp n lo hi lam δ := by
  intro x x' hx hx' hl hu
  obtain ⟨j, hj, hcell⟩ := overlap_cell_contains h ⟨hl, hu⟩
  exact hlocal j hj x x' hx hx' hcell.1 hcell.2

/-- The two deterministic selections cover the full sixty-by-twelve grid.
This assertion includes shared cell endpoints. It contributes no probability charge. -/
theorem theta_overlap_cells {n : ℕ} (hn : 0 < n) {a b lo hi : ℝ}
    (hab : a ≤ b) (hlh : lo ≤ hi) (w : Window)
    (hg : ∀ θ ∈ Set.Icc a b, OverlapGuard n θ w lo hi)
    {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ : BstLean.Part150.thetaC c τ ∈ Set.Icc a b)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ BstLean.Part182.GammaS c w.t w.z w.pair) :
    ∃ i < 60, ∃ j < 12,
      BstLean.Part150.thetaC c τ ∈ (thetaCover a b hab).cell i ∧
      dotProduct (BstLean.Part130.sphPt (c + τ • p.1))
        (BstLean.Part130.sphPt (c + τ • p.2)) ∈ (overlapCover lo hi hlh).cell j := by
  obtain ⟨i, hi, hcell⟩ := (thetaCover a b hab).covers _ hθ
  obtain ⟨j, hj, hpair⟩ := pair_cell_contains hn hτ w hlh (hg _ hθ) hp
  exact ⟨i, Finset.mem_range.mp hi, j, hj, hcell, hpair⟩

end BstLean.Part235
