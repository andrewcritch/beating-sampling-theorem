import BstLean.Part36Defs

/-!
# Part 36, wave 1: the coefficient count and sphere moments of multiset monomials (light)

* `card_coefIdxD`: `card (CoefIdxD n d) = n · C(n+d, d)` (Mathlib's `Sym.card_sym_eq_choose` and the hockey
  stick `Σ_{i ≤ d} C(n+i−1, i) = C(n+d, d)`).
* `sphere_multiset`: `SphereProd n R μ` gives, for a multiset monomial of degree `≤ R`, integrability and
  `∫ x^s = gpm s / ρ_{|s|/2}`. Route: write `s = Multiset.map τ univ` for `τ : Fin (card s) → Fin n`
  (for example from `s.toList`), so that `x^s = ∏ x (τ i)` and `count l s = #{i | τ i = l}`.

Depends on `Part36Defs` only. Provers must not use `native_decide`.
-/

namespace BstLean.Part36

open MeasureTheory
open BstLean.Part33 (SphereProd)

variable {n d : ℕ}

theorem card_coefIdxD (n d : ℕ) : Fintype.card (CoefIdxD n d) = n * (n + d).choose d := by
  classical
  simp only [CoefIdxD, Fintype.card_sigma, Fintype.card_prod,
    Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range]
  rw [Nat.sum_range_multichoose, ← Nat.choose_symm_add (a := d) (b := n)]
  simp [Nat.add_comm, Nat.mul_comm]

theorem DD_eq (n d : ℕ) : DD n d = (n : ℝ) * ((n + d).choose d : ℝ) := by
  unfold DD
  rw [card_coefIdxD]
  push_cast
  rfl

theorem DD_pos (hn : 1 ≤ n) : 0 < DD n d := by
  rw [DD_eq]
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : 0 < (n + d).choose d := Nat.choose_pos (by omega)
  exact mul_pos hn' (by exact_mod_cast hc)

theorem sphere_multiset {R : ℕ} (μ : Measure (Fin n → ℝ)) (hμ : SphereProd n R μ)
    (s : Multiset (Fin n)) (hs : Multiset.card s ≤ R) :
    Integrable (fun x => monoVal x s) μ ∧
      ∫ x, monoVal x s ∂μ = gpm s / rhoD n (Multiset.card s / 2) := by
  classical
  have enum : ∃ (r : ℕ) (τ : Fin r → Fin n), r = s.card ∧
      Finset.univ.val.map τ = s := by
    induction s using Quot.inductionOn with
    | h l =>
      refine ⟨l.length, l.get, rfl, ?_⟩
      simp [Fin.univ_val_map]
  obtain ⟨r, τ, hr, hτ⟩ := enum
  have hv (x : Fin n → ℝ) : monoVal x s = ∏ i, x (τ i) := by
    rw [monoVal, ← hτ, Multiset.map_map]
    rfl
  have hc (l : Fin n) : s.count l = (Finset.univ.filter fun i => τ i = l).card := by
    rw [← hτ, Multiset.count_map]
    simp only [← Finset.filter_val, Finset.card_val, eq_comm]
  constructor
  · simpa only [hv] using hμ.integ r (hr ▸ hs) τ
  · simpa only [hv, gpm, hc, rhoD, hr] using hμ.mom r (hr ▸ hs) τ

end BstLean.Part36
