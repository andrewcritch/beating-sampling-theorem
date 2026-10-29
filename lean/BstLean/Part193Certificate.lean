import BstLean.Part193Cover
import BstLean.Part193Expr

/-! Part 193: the formula certificate and finite cover junction.
Formula identities remain explicit premises. Each cell supplies a proof tree
for the exact expression and a checked bound for its upper endpoint. -/
namespace BstLean.Part193

theorem finite_cover_expr_upper {α ι : Type*} {domain : Set α}
    (C : FiniteCover α ι domain) (v : α → ℕ → ℝ) (a : Expr) (I : ι → Interval)
    (hcert : ∀ i ∈ C.indices, ∀ x ∈ domain, x ∈ C.cell i →
      ExprCertificate (v x) a (I i)) {U : ℝ}
    (hupper : ∀ i ∈ C.indices, (I i).hi ≤ U) :
    ∀ x ∈ domain, a.eval (v x) ≤ U := by
  apply finite_cover_uniform_upper C (f := fun x => a.eval (v x))
    ⟨I, fun i hi x hx hcell => (hcert i hi x hx hcell).sound⟩ hupper

/-- A proved formula identity connects the certificate to the intended scalar. -/
theorem finite_cover_formula_upper {α ι : Type*} {domain : Set α}
    (C : FiniteCover α ι domain) (v : α → ℕ → ℝ) (a : Expr) (I : ι → Interval)
    (f : α → ℝ) (hformula : ∀ x ∈ domain, f x = a.eval (v x))
    (hcert : ∀ i ∈ C.indices, ∀ x ∈ domain, x ∈ C.cell i →
      ExprCertificate (v x) a (I i)) {U : ℝ}
    (hupper : ∀ i ∈ C.indices, (I i).hi ≤ U) :
    ∀ x ∈ domain, f x ≤ U := by
  intro x hx
  rw [hformula x hx]
  exact finite_cover_expr_upper C v a I hcert hupper x hx

/-- Taking the minimum of two proved upper bounds retains both proofs. -/
theorem upper_min {x a b : ℝ} (ha : x ≤ a) (hb : x ≤ b) : x ≤ min a b :=
  le_min ha hb

/-- A cell can select either complete certificate for the same scalar. -/
theorem finite_cover_alternative_upper {α ι : Type*} {domain : Set α}
    (C : FiniteCover α ι domain) {f : α → ℝ} (a b : ι → ℝ) {U : ℝ}
    (hcell : ∀ i ∈ C.indices, ∀ x ∈ domain, x ∈ C.cell i →
      (f x ≤ a i ∧ a i ≤ U) ∨ (f x ≤ b i ∧ b i ≤ U)) :
    ∀ x ∈ domain, f x ≤ U := by
  apply finite_cover_property C (P := fun x => f x ≤ U)
  intro i hi x hx hxi
  rcases hcell i hi x hx hxi with h | h
  · exact h.1.trans h.2
  · exact h.1.trans h.2

end BstLean.Part193
