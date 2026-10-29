import BstLean.Part56MomProg_Toolkit
import BstLean.Part56MomProg_Polynomial

/-! The index of monomials of degree at most `D`, coefficient vectors, and their products. -/

namespace BstLean.Part56.MomProg

open MvPolynomial
open BstLean.Part41 (Mono)

variable {n : ℕ}

/-- The degree of an exponent vector. -/
def fdeg (μ : Fin n →₀ ℕ) : ℕ := μ.sum fun _ e => e

theorem fdeg_add (μ ν : Fin n →₀ ℕ) : fdeg (μ + ν) = fdeg μ + fdeg ν := by
  unfold fdeg
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem fdeg_zero : fdeg (0 : Fin n →₀ ℕ) = 0 := by simp [fdeg]

theorem fdeg_single (l : Fin n) (e : ℕ) : fdeg (Finsupp.single l e) = e := by
  simp [fdeg, Finsupp.sum_single_index]

/-- Exponent vectors of degree at most `D`. -/
abbrev Idx (n D : ℕ) := {μ : Fin n →₀ ℕ // fdeg μ ≤ D}

noncomputable def Idx.toMono {D : ℕ} (μ : Idx n D) : Mono n D :=
  ⟨⟨fdeg μ.1, Nat.lt_succ_of_le μ.2⟩, ⟨Finsupp.toMultiset μ.1, by
    simp [Finsupp.card_toMultiset, fdeg]; rfl⟩⟩

theorem Idx.toMono_injective {D : ℕ} : Function.Injective (Idx.toMono (n := n) (D := D)) := by
  intro a b h
  have h2 := congrArg (fun p : Mono n D => (p.2 : Multiset (Fin n))) h
  have h3 : Finsupp.toMultiset a.1 = Finsupp.toMultiset b.1 := by
    have := h2
    simp only [Idx.toMono] at this
    exact HEq.eq (by
      have e : fdeg a.1 = fdeg b.1 := by
        have := congrArg (fun p : Mono n D => (p.1 : ℕ)) h
        simpa [Idx.toMono] using this
      exact heq_of_eq this)
  apply Subtype.ext
  have := congrArg Multiset.toFinsupp h3
  simpa using this

noncomputable instance (D : ℕ) : Fintype (Idx n D) :=
  Fintype.ofInjective _ (Idx.toMono_injective (n := n) (D := D))


lemma card_mono' (n d : ℕ) : Fintype.card (Mono n d) = (n + d).choose d := by
  classical
  simp only [Mono, Fintype.card_sigma, Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range, Nat.sum_range_multichoose,
    ← Nat.choose_symm_add (a := d) (b := n)]
  simp [Nat.add_comm]

lemma choose_le_pow' (n : ℕ) : ∀ d : ℕ, (n + d).choose d ≤ (n + 1) ^ d
  | 0 => by simp
  | d + 1 => by
    have ih := choose_le_pow' n d
    have h := Nat.add_one_mul_choose_eq (n + d) d
    have h2 : (n + (d + 1)).choose (d + 1) * (d + 1) ≤ (n + 1) ^ (d + 1) * (d + 1) := by
      rw [show n + (d + 1) = (n + d) + 1 by omega, ← h, pow_succ]
      calc (n + d + 1) * (n + d).choose d ≤ ((n + 1) * (d + 1)) * (n + 1) ^ d := by
            apply Nat.mul_le_mul _ ih
            nlinarith
        _ = (n + 1) ^ d * (n + 1) * (d + 1) := by ring
    exact Nat.le_of_mul_le_mul_right h2 (by omega)

theorem card_Idx_le (n D : ℕ) : Fintype.card (Idx n D) ≤ (n + 1) ^ D := by
  have h := Fintype.card_le_of_injective _ (Idx.toMono_injective (n := n) (D := D))
  rw [card_mono'] at h
  exact h.trans (choose_le_pow' n D)

/-- The zero exponent. -/
def Idx.zero (D : ℕ) : Idx n D := ⟨0, by simp [fdeg_zero]⟩

/-! ## Coefficient vectors -/

/-- A vector represents a polynomial on the index. -/
def Rep {D : ℕ} (c : Idx n D → ℝ) (Q : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ μ : Idx n D, c μ = Q.coeff μ.1

/-- Extension by zero. -/
noncomputable def ext0 {D : ℕ} (c : Idx n D → ℝ) (ν : Fin n →₀ ℕ) : ℝ :=
  if h : fdeg ν ≤ D then c ⟨ν, h⟩ else 0

/-- The truncated product of two vectors. -/
noncomputable def pmul {D : ℕ} (c₁ c₂ : Idx n D → ℝ) (μ : Idx n D) : ℝ :=
  ∑ x : (Finset.HasAntidiagonal.antidiagonal μ.1 : Set ((Fin n →₀ ℕ) × (Fin n →₀ ℕ))),
    ext0 c₁ x.1.1 * ext0 c₂ x.1.2

theorem antidiag_le {D : ℕ} (μ : Idx n D) {x : (Fin n →₀ ℕ) × (Fin n →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal μ.1) : fdeg x.1 ≤ D ∧ fdeg x.2 ≤ D := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h := fdeg_add x.1 x.2
  rw [hx] at h
  have := μ.2
  constructor <;> omega

theorem rep_mul {D : ℕ} {c₁ c₂ : Idx n D → ℝ} {P Q : MvPolynomial (Fin n) ℝ}
    (h₁ : Rep c₁ P) (h₂ : Rep c₂ Q) : Rep (pmul c₁ c₂) (P * Q) := by
  classical
  intro μ
  rw [coeff_mul, pmul]
  rw [← Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal μ.1)]
  apply Fintype.sum_congr
  intro x
  obtain ⟨hx1, hx2⟩ := antidiag_le μ x.2
  simp only [ext0, hx1, hx2, dite_true]
  rw [h₁ ⟨_, hx1⟩, h₂ ⟨_, hx2⟩]

theorem card_antidiag_le {D : ℕ} (μ : Idx n D) :
    Fintype.card (Finset.HasAntidiagonal.antidiagonal μ.1 : Set ((Fin n →₀ ℕ) × (Fin n →₀ ℕ))) ≤
      Fintype.card (Idx n D) * Fintype.card (Idx n D) := by
  classical
  let f : (Finset.HasAntidiagonal.antidiagonal μ.1 : Set ((Fin n →₀ ℕ) × (Fin n →₀ ℕ))) → Idx n D × Idx n D :=
    fun x => (⟨x.1.1, (antidiag_le μ x.2).1⟩, ⟨x.1.2, (antidiag_le μ x.2).2⟩)
  have hf : Function.Injective f := by
    intro x y h
    have h1 := congrArg (fun p => p.1.1) h
    have h2 := congrArg (fun p => p.2.1) h
    exact Subtype.ext (Prod.ext h1 h2)
  have := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod] using this

/-- The vector of the constant `1`. -/
noncomputable def oneVec {D : ℕ} (μ : Idx n D) : ℝ := if μ.1 = 0 then 1 else 0

theorem rep_one {D : ℕ} : Rep (oneVec (n := n) (D := D)) 1 := by
  intro μ
  simp [oneVec, coeff_one, eq_comm]

/-- The vector of the linear form `Σ_l a_l X_l`. -/
noncomputable def linVec {D : ℕ} (a : Fin n → ℝ) (μ : Idx n D) : ℝ :=
  if h : ∃ l, μ.1 = Finsupp.single l 1 then a h.choose else 0

theorem rep_lin {D : ℕ} (a : Fin n → ℝ) :
    Rep (linVec (D := D) a) (∑ l, C (a l) * X l) := by
  classical
  intro μ
  rw [coeff_sum]
  simp only [coeff_C_mul, coeff_X']
  unfold linVec
  split_ifs with h
  · rw [Finset.sum_eq_single h.choose]
    · rw [if_pos h.choose_spec.symm, mul_one]
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro hb'
      apply hb
      have := h.choose_spec
      rw [this] at hb'
      exact (Finsupp.single_left_inj one_ne_zero).mp hb'
    · simp
  · symm
    apply Finset.sum_eq_zero
    intro l _
    rw [if_neg, mul_zero]
    intro hl
    exact h ⟨l, hl.symm⟩

/-- Scalar multiple. -/
theorem rep_smul {D : ℕ} {c : Idx n D → ℝ} {Q : MvPolynomial (Fin n) ℝ} (r : ℝ)
    (h : Rep c Q) : Rep (fun μ => r * c μ) (C r * Q) := by
  intro μ; show r * c μ = _; rw [coeff_C_mul, h]

theorem rep_add {D : ℕ} {c₁ c₂ : Idx n D → ℝ} {P Q : MvPolynomial (Fin n) ℝ}
    (h₁ : Rep c₁ P) (h₂ : Rep c₂ Q) : Rep (fun μ => c₁ μ + c₂ μ) (P + Q) := by
  intro μ; show c₁ μ + c₂ μ = _; rw [MvPolynomial.coeff_add, h₁, h₂]

theorem rep_sub {D : ℕ} {c₁ c₂ : Idx n D → ℝ} {P Q : MvPolynomial (Fin n) ℝ}
    (h₁ : Rep c₁ P) (h₂ : Rep c₂ Q) : Rep (fun μ => c₁ μ - c₂ μ) (P - Q) := by
  intro μ; show c₁ μ - c₂ μ = _; rw [MvPolynomial.coeff_sub, h₁, h₂]

theorem rep_sum {D : ℕ} {ι : Type} (s : Finset ι) {c : ι → Idx n D → ℝ}
    {P : ι → MvPolynomial (Fin n) ℝ} (h : ∀ i ∈ s, Rep (c i) (P i)) :
    Rep (fun μ => ∑ i ∈ s, c i μ) (∑ i ∈ s, P i) := by
  intro μ; show ∑ i ∈ s, c i μ = _; rw [MvPolynomial.coeff_sum]; exact Finset.sum_congr rfl (fun i hi => h i hi μ)

/-- The product of a list of vectors. -/
noncomputable def plist {D : ℕ} : List (Idx n D → ℝ) → Idx n D → ℝ
  | [] => oneVec
  | c :: cs => pmul c (plist cs)

theorem rep_plist {D : ℕ} {ι : Type} (c : ι → Idx n D → ℝ) (P : ι → MvPolynomial (Fin n) ℝ)
    (h : ∀ i, Rep (c i) (P i)) (l : List ι) :
    Rep (plist (l.map c)) (l.map P).prod := by
  induction l with
  | nil => exact rep_one
  | cons a l ih => exact rep_mul (h a) ih

end BstLean.Part56.MomProg
