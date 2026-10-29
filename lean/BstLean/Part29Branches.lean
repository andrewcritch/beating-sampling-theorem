import BstLean.Part29HeatError
import BstLean.Part29Index
import BstLean.Part29Certificate

/-!
# Part 29, final assembly: the branches as centred quadratic forms

On the coefficient space `CoefIdx n`, the heat program `Hof` and the `O(n²)` program `Uof` have errors
`B − g = Mᵀ A M − tr A / D` on the unit sphere (`D = |CoefIdx n|`), for explicit symmetric matrices `A_H`, `A_U`,
with `‖A_H‖_F² = 4 v ‖Λ‖² / (n²(n+2)²)` and `‖A_U‖_F² = v · s_n` (`v = ‖F‖_F²`, `‖Λ‖² = Lam n`, `s_n = sN n`).
-/

namespace BstLean.Part29

open MeasureTheory

variable {n : ℕ}

/-- Read the constants, linear and quadratic raw coefficients out of a coefficient vector. -/
def cOf (M : CoefIdx n → ℝ) : Fin n → ℝ := fun k => M (Sum.inl k)
def LOf (M : CoefIdx n → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun k i => M (Sum.inr (Sum.inl (k, i)))
noncomputable def aOf (M : CoefIdx n → ℝ) : Fin n → Fin n → Fin n → ℝ := fun k i j =>
  if h : i ≤ j then M (Sum.inr (Sum.inr ⟨(i, j, k), h⟩)) else 0

/-- `B(M) = E_x f(m_M(x))`. -/
noncomputable def Bof (μ : Measure (Fin n → ℝ)) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (M : CoefIdx n → ℝ) : ℝ :=
  ∫ x, funF f0 g F (mapM (cOf M) (LOf M) (fun k => symOfRaw (aOf M k)) x) ∂μ

/-- The part of the exact formula that both approximate branches keep. -/
noncomputable def keptOf (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ) : ℝ :=
  let t : Fin n → ℝ := fun k => ∑ i, symOfRaw (aOf M k) i i
  let ν : Fin n → ℝ := fun k => cOf M k + t k / n
  f0 + ∑ k, g k * ν k + ∑ k, ∑ l, F k l * ν k * ν l

/-- The heat matrix: `F ⊗ (2/(n(n+2))) Λ` on the quadratic block, `0` elsewhere
(`Λ` has weight `1` on squares, `1/2` on cross monomials). -/
noncomputable def AH (F : Matrix (Fin n) (Fin n) ℝ) : Matrix (CoefIdx n) (CoefIdx n) ℝ := fun α β =>
  match α, β with
  | Sum.inr (Sum.inr p), Sum.inr (Sum.inr q) =>
      if p.1.1 = q.1.1 ∧ p.1.2.1 = q.1.2.1 then
        F p.1.2.2 q.1.2.2 * (2 / ((n : ℝ) * (n + 2))) * (if p.1.1 = p.1.2.1 then 1 else 1 / 2)
      else 0
  | _, _ => 0

/-- The `O(n²)` matrix: `F ⊗ I / n` on the linear block, `F ⊗ Σ_q` on the quadratic block, with
`Σ_q(p, p') = (2/(n(n+2))) (w_p [p = p'] − [p, p' diagonal] / n)`. -/
noncomputable def AU (F : Matrix (Fin n) (Fin n) ℝ) : Matrix (CoefIdx n) (CoefIdx n) ℝ := fun α β =>
  match α, β with
  | Sum.inr (Sum.inl (k, i)), Sum.inr (Sum.inl (l, i')) => if i = i' then F k l / n else 0
  | Sum.inr (Sum.inr p), Sum.inr (Sum.inr q) =>
      F p.1.2.2 q.1.2.2 * (2 / ((n : ℝ) * (n + 2))) *
        ((if p.1.1 = q.1.1 ∧ p.1.2.1 = q.1.2.1 then (if p.1.1 = p.1.2.1 then 1 else 1 / 2) else 0)
          - (if p.1.1 = p.1.2.1 ∧ q.1.1 = q.1.2.1 then 1 / (n : ℝ) else 0))
  | _, _ => 0

/-- The quadratic form `Mᵀ A M` on the coefficient space. -/
def qformC (A : Matrix (CoefIdx n) (CoefIdx n) ℝ) (M : CoefIdx n → ℝ) : ℝ := ∑ α, ∑ β, A α β * M α * M β

/-- The heat program `Hof = kept + ⟨F, L Lᵀ⟩/n + 2/(n(n+2)) (tr A_H / D·(n(n+2)/2) … )`: stated as kept part plus
the exact linear and trace terms plus the mean `tr A_H / D` of the Gram part. -/
noncomputable def Hof (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ) : ℝ :=
  let t : Fin n → ℝ := fun k => ∑ i, symOfRaw (aOf M k) i i
  keptOf f0 g F M + (∑ k, ∑ l, F k l * ∑ i, LOf M k i * LOf M l i) / n
    + (AH F).trace / Fintype.card (CoefIdx n)
    - 2 / ((n : ℝ) * (n + 2)) * ((∑ k, ∑ l, F k l * t k * t l) / n)

/-- The `O(n²)` program `Uof = kept + tr A_U / D`. -/
noncomputable def Uof (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ) : ℝ :=
  keptOf f0 g F M + (AU F).trace / Fintype.card (CoefIdx n)

private abbrev MonoIdx (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

private def quadEquiv : {p : Fin n × Fin n × Fin n // p.1 ≤ p.2.1} ≃ MonoIdx n × Fin n where
  toFun p := (⟨(p.val.1,p.val.2.1),p.property⟩,p.val.2.2)
  invFun p := ⟨(p.1.val.1,p.1.val.2,p.2),p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma sum_quad (f : {p : Fin n × Fin n × Fin n // p.1 ≤ p.2.1} → ℝ) :
    (∑ p, f p) = ∑ p : MonoIdx n, ∑ k, f ⟨(p.val.1,p.val.2,k),p.property⟩ := by
  classical
  rw [← quadEquiv.symm.sum_comp, Fintype.sum_prod_type]
  rfl

private lemma mono_eq (p q : MonoIdx n) :
    (p.val.1 = q.val.1 ∧ p.val.2 = q.val.2) ↔ p = q := by
  constructor
  · rintro ⟨h₁,h₂⟩; exact Subtype.ext (Prod.ext h₁ h₂)
  · rintro rfl; exact ⟨rfl,rfl⟩

private noncomputable def raw (M : CoefIdx n → ℝ) (p : MonoIdx n) (k : Fin n) : ℝ :=
  M (Sum.inr (Sum.inr ⟨(p.val.1,p.val.2,k),p.property⟩))

private noncomputable def weight (p : MonoIdx n) : ℝ :=
  if p.val.1 = p.val.2 then 1 else 1/2

private lemma sum_mono (f : Fin n → Fin n → ℝ) :
    (∑ p : MonoIdx n, f p.val.1 p.val.2) =
      ∑ i, ∑ j, if i ≤ j then f i j else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2))
    (by simp) (fun p => f p.1 p.2)]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]

private lemma gram_mono (M : CoefIdx n → ℝ) (k l : Fin n) :
    (∑ p : MonoIdx n, weight p * raw M p k * raw M p l) =
      ∑ i, aOf M k i i * aOf M l i i +
        (1/2) * ∑ i, ∑ j, if i < j then aOf M k i j * aOf M l i j else 0 := by
  classical
  have h : (∑ p : MonoIdx n, weight p * raw M p k * raw M p l) =
      ∑ p : MonoIdx n, (if p.val.1 = p.val.2 then 1 else 1/2) *
        aOf M k p.val.1 p.val.2 * aOf M l p.val.1 p.val.2 := by
    apply Finset.sum_congr rfl
    intro p _
    simp [weight, raw, aOf, p.property]
  rw [h, sum_mono (fun i j => (if i = j then 1 else 1/2) *
    aOf M k i j * aOf M l i j)]
  have term (i j : Fin n) :
      (if i ≤ j then (if i = j then 1 else 1/2) * aOf M k i j * aOf M l i j else 0) =
      (if i = j then aOf M k i i * aOf M l i i else 0) +
        (1/2) * (if i < j then aOf M k i j * aOf M l i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h.le, h, ne_of_lt h, mul_assoc]
    · subst j; simp
    · simp [not_le.mpr h, not_lt.mpr h.le, ne_of_gt h]
  simp_rw [term, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

private lemma qform_AH (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ) :
    qformC (AH F) M = ∑ p : MonoIdx n, ∑ k, ∑ l,
      F k l * (2 / ((n : ℝ) * (n + 2))) * weight p * raw M p k * raw M p l := by
  classical
  unfold qformC
  simp only [Fintype.sum_sum_type, AH, zero_mul, Finset.sum_const_zero, zero_add,
    add_zero]
  simp_rw [sum_quad]
  simp only [mono_eq, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

private lemma qform_AH_gram (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ) :
    qformC (AH F) M = 2 / ((n : ℝ) * (n + 2)) * gramRaw F (aOf M) := by
  rw [qform_AH]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (MonoIdx n)))]
  unfold gramRaw
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [← gram_mono M k l]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

private lemma sum_diag (f : MonoIdx n → ℝ) :
    (∑ p, if p.val.1 = p.val.2 then f p else 0) =
      ∑ i : Fin n, f ⟨(i,i),le_rfl⟩ := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun i _ => (⟨(i,i),le_rfl⟩ : MonoIdx n)) ?_ ?_ ?_ ?_
  · simp
  · intro i _ j _ h
    exact congrArg (fun p : MonoIdx n => p.val.1) h
  · intro p hp
    have h : p.val.1 = p.val.2 := (Finset.mem_filter.mp hp).2
    refine ⟨p.val.1, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl h
  · intro i _; rfl

private lemma sum_weight_sq : (∑ p : MonoIdx n, weight p ^ 2) = Lam n := by
  classical
  have count : (∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0) =
      (n : ℝ) * (n - 1) / 2 := by
    have term (i j : Fin n) :
        (if i < j then (1 : ℝ) else 0) + (if j < i then 1 else 0) +
          (if i = j then 1 else 0) = 1 := by
      rcases lt_trichotomy i j with h | h | h <;> simp [h, ne_of_lt, ne_of_gt,
        not_lt_of_ge, le_of_lt, eq_comm]
    have hs := congrArg (fun f : Fin n → Fin n → ℝ => ∑ i, ∑ j, f i j)
      (funext fun i => funext fun j => term i j)
    simp only [Finset.sum_add_distrib] at hs
    rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then (1 : ℝ) else 0)] at hs
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
    nlinarith
  have h : (∑ p : MonoIdx n, weight p ^ 2) =
      ∑ p : MonoIdx n, (if p.val.1 = p.val.2 then (1 : ℝ) else 1/2)^2 := rfl
  rw [h, sum_mono (fun i j => (if i = j then (1 : ℝ) else 1/2)^2)]
  have term (i j : Fin n) :
      (if i ≤ j then (if i = j then (1 : ℝ) else 1/2)^2 else 0) =
        (if i = j then (1 : ℝ) else 0) + (1/4)*(if i < j then 1 else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h.le, h, ne_of_lt h]; norm_num
    · subst j; simp
    · simp [not_le.mpr h, not_lt.mpr h.le, ne_of_gt h]
  simp_rw [term, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [count]
  unfold Lam
  ring

private lemma swap_four {ι κ ρ τ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    [Fintype τ] (f : ι → κ → ρ → τ → ℝ) :
    (∑ i, ∑ k, ∑ j, ∑ l, f i k j l) = ∑ k, ∑ l, ∑ i, ∑ j, f i k j l := by
  rw [Finset.sum_comm]

  apply Finset.sum_congr rfl
  intro k _
  simp_rw [Finset.sum_comm (f := fun j l => f _ k j l)]
  rw [Finset.sum_comm]

private lemma factor_blocks (F : Matrix (Fin n) (Fin n) ℝ)
    (K : MonoIdx n → MonoIdx n → ℝ) :
    (∑ p, ∑ k, ∑ q, ∑ l, (F k l * K p q)^2) =
      (∑ k, ∑ l, F k l ^ 2) * ∑ p, ∑ q, K p q ^ 2 := by
  rw [swap_four]
  simp only [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]

private lemma frob_AH_factor (F : Matrix (Fin n) (Fin n) ℝ) :
    (∑ α, ∑ β, AH F α β ^ 2) =
      (∑ k, ∑ l, F k l ^ 2) * (2 / ((n : ℝ) * (n+2)))^2 * Lam n := by
  classical
  simp only [Fintype.sum_sum_type, AH, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, zero_add, add_zero]
  simp_rw [sum_quad]
  have h : (∑ p : MonoIdx n, ∑ k, ∑ q : MonoIdx n, ∑ l,
      (if p.val.1 = q.val.1 ∧ p.val.2 = q.val.2 then
        F k l * (2 / ((n : ℝ) * (n+2))) * weight p else 0)^2) =
      (∑ k, ∑ l, F k l ^ 2) *
        ∑ p : MonoIdx n, ∑ q : MonoIdx n,
          (if p = q then (2 / ((n : ℝ) * (n+2))) * weight p else 0)^2 := by
    rw [← factor_blocks]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro l _
    simp only [mono_eq]
    by_cases hp : p = q <;> simp [hp, mul_assoc]
  conv_lhs at h => simp only [weight]
  rw [h]
  simp only [ite_pow, zero_pow (by decide : 2 ≠ 0), Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, mul_pow, ← Finset.mul_sum, sum_weight_sq]
  ring

private noncomputable def diagD (p : MonoIdx n) : ℝ :=
  if p.val.1 = p.val.2 then 1 else 0

private lemma sum_diagD : (∑ p : MonoIdx n, diagD p) = n := by
  classical
  unfold diagD
  rw [sum_diag]
  simp

private lemma cov_norm (hn : 1 ≤ n) :
    (∑ p : MonoIdx n, ∑ q : MonoIdx n,
      ((if p = q then weight p else 0) - diagD p * diagD q / n)^2) = Lam n - 1 := by
  classical
  have term (p q : MonoIdx n) :
      ((if p = q then weight p else 0) - diagD p * diagD q / n)^2 =
        (if p = q then weight p ^ 2 else 0) -
          (2 / n) * (if p = q then diagD p else 0) +
          diagD p * diagD q / (n : ℝ)^2 := by
    by_cases h : p = q
    · subst q
      by_cases hd : p.val.1 = p.val.2 <;>
        simp [hd, diagD, weight, div_pow, div_eq_mul_inv] <;> ring
    · by_cases hp : p.val.1 = p.val.2 <;> by_cases hq : q.val.1 = q.val.2 <;>
        simp [h, hp, hq, diagD, weight, div_pow, div_eq_mul_inv]
  simp_rw [term, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_div]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, sum_weight_sq,
    sum_diagD, ← Finset.sum_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_diagD]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  field_simp
  ring

private lemma frob_AU_factor (hn : 1 ≤ n) (F : Matrix (Fin n) (Fin n) ℝ) :
    (∑ α, ∑ β, AU F α β ^ 2) =
      (∑ k, ∑ l, F k l ^ 2) / n +
        (∑ k, ∑ l, F k l ^ 2) * (2 / ((n : ℝ) * (n+2)))^2 * (Lam n - 1) := by
  classical
  simp only [Fintype.sum_sum_type, AU, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, zero_add, add_zero, Fintype.sum_prod_type]
  simp_rw [sum_quad]
  have quad : (∑ p : MonoIdx n, ∑ k, ∑ q : MonoIdx n, ∑ l,
      (F k l * (2 / ((n : ℝ) * (n+2))) *
        ((if p.val.1 = q.val.1 ∧ p.val.2 = q.val.2 then weight p else 0) -
          (if p.val.1 = p.val.2 ∧ q.val.1 = q.val.2 then 1/(n : ℝ) else 0)))^2) =
        (∑ k, ∑ l, F k l ^ 2) * (2 / ((n : ℝ) * (n+2)))^2 * (Lam n - 1) := by
    have h : (∑ p : MonoIdx n, ∑ k, ∑ q : MonoIdx n, ∑ l,
      (F k l * (2 / ((n : ℝ) * (n+2))) *
        ((if p.val.1 = q.val.1 ∧ p.val.2 = q.val.2 then weight p else 0) -
          (if p.val.1 = p.val.2 ∧ q.val.1 = q.val.2 then 1/(n : ℝ) else 0)))^2) =
        (∑ k, ∑ l, F k l ^ 2) *
          ∑ p : MonoIdx n, ∑ q : MonoIdx n,
            ((2 / ((n : ℝ) * (n+2))) *
              ((if p = q then weight p else 0) - diagD p * diagD q / n))^2 := by
      rw [← factor_blocks]
      apply Finset.sum_congr rfl; intro p _
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro q _
      apply Finset.sum_congr rfl; intro l _
      simp only [mono_eq]
      by_cases hp : p.val.1 = p.val.2 <;> by_cases hq : q.val.1 = q.val.2 <;>
        simp [hp, hq, diagD, mul_assoc]
    rw [h]
    simp only [mul_pow, ← Finset.mul_sum, cov_norm hn]
    ring
  simp only [weight] at quad
  rw [quad]
  congr 1
  simp only [ite_pow, zero_pow (by decide : 2 ≠ 0), Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, div_pow]
  simp_rw [Finset.sum_comm (f := fun i l : Fin n => (F _ l)^2 / (n : ℝ)^2)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.sum_div]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  field_simp

private lemma qform_AU (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ) :
    qformC (AU F) M =
      (∑ k, ∑ l, F k l * ∑ i, LOf M k i * LOf M l i) / n + qformC (AH F) M -
      2 / ((n : ℝ) * (n + 2)) *
        ((∑ k, ∑ l, F k l * (∑ i, symOfRaw (aOf M k) i i) *
          (∑ i, symOfRaw (aOf M l) i i)) / n) := by
  classical
  unfold qformC
  simp only [Fintype.sum_sum_type, AU, AH, zero_mul, Finset.sum_const_zero,
    zero_add, add_zero, Fintype.sum_prod_type]
  simp_rw [sum_quad]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mono_eq, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, ite_and]
  simp_rw [sum_diag]
  simp only [symOfRaw, if_true, aOf, le_refl, dite_true, LOf]
  rw [← add_sub_assoc]
  congr 1
  · congr 1
    simp only [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [swap_four]
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem AH_isSymm (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) : (AH F).IsSymm := by
  classical
  apply Matrix.IsSymm.ext
  intro α β
  rcases α with k | k | p <;> rcases β with l | l | q <;> simp only [AH]
  by_cases h : p.val.1 = q.val.1 ∧ p.val.2.1 = q.val.2.1
  · obtain ⟨hi, hj⟩ := h
    simp [hi, hj, hF.apply]
  · have h' : ¬ (q.val.1 = p.val.1 ∧ q.val.2.1 = p.val.2.1) := by
      simpa only [eq_comm] using h
    simp [h, h']

theorem AU_isSymm (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) : (AU F).IsSymm := by
  classical
  apply Matrix.IsSymm.ext
  intro α β
  rcases α with k | k | p <;> rcases β with l | l | q <;> simp only [AU]
  · simp [eq_comm, hF.apply]
  · by_cases h : p.val.1 = q.val.1 ∧ p.val.2.1 = q.val.2.1
    · obtain ⟨hi, hj⟩ := h
      simp [hi, hj, hF.apply, and_comm]
    · have h' : ¬ (q.val.1 = p.val.1 ∧ q.val.2.1 = p.val.2.1) := by
        simpa only [eq_comm] using h
      simp [h, h', hF.apply, and_comm]

/-- **The heat branch's error is centred:** on the unit sphere, `B − Hof = Mᵀ A_H M − tr A_H / D`. -/
theorem heat_centred (hn : 1 ≤ n) (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : SphereMoments n μ) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (M : CoefIdx n → ℝ) (hM : ∑ α, M α ^ 2 = 1) :
    Bof μ f0 g F M - Hof f0 g F M =
      qformC (AH F) M - (AH F).trace / Fintype.card (CoefIdx n) := by
  have h := exact_formula hn μ hμ (cOf M) (LOf M) (fun k => symOfRaw (aOf M k))
    (fun k => symOfRaw_isSymm _) f0 g F hF
  dsimp only at h
  unfold Bof Hof keptOf
  rw [h, qform_AH_gram]
  have hK : (∑ k, ∑ l, F k l *
      (∑ i, ∑ j, symOfRaw (aOf M k) i j * symOfRaw (aOf M l) j i)) =
      gramRaw F (aOf M) := by
    unfold gramRaw
    simp_rw [trace_mul_symOfRaw]
  rw [hK]
  ring

/-- **The `O(n²)` branch's error is centred:** on the unit sphere, `B − Uof = Mᵀ A_U M − tr A_U / D`. -/
theorem U2_centred (hn : 1 ≤ n) (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : SphereMoments n μ) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (M : CoefIdx n → ℝ) (hM : ∑ α, M α ^ 2 = 1) :
    Bof μ f0 g F M - Uof f0 g F M =
      qformC (AU F) M - (AU F).trace / Fintype.card (CoefIdx n) := by
  have h := exact_formula hn μ hμ (cOf M) (LOf M) (fun k => symOfRaw (aOf M k))
    (fun k => symOfRaw_isSymm _) f0 g F hF
  dsimp only at h
  unfold Bof Uof keptOf
  rw [h, qform_AU, qform_AH_gram]
  have hK : (∑ k, ∑ l, F k l *
      (∑ i, ∑ j, symOfRaw (aOf M k) i j * symOfRaw (aOf M l) j i)) =
      gramRaw F (aOf M) := by
    unfold gramRaw
    simp_rw [trace_mul_symOfRaw]
  rw [hK]
  ring

/-- `‖A_H‖_F² = 4 v ‖Λ‖² / (n²(n+2)²)`. -/
theorem AH_frob (hn : 1 ≤ n) (F : Matrix (Fin n) (Fin n) ℝ) :
    ∑ α, ∑ β, AH F α β ^ 2 =
      4 * (∑ k, ∑ l, F k l ^ 2) * Lam n / ((n : ℝ) ^ 2 * (n + 2) ^ 2) := by
  rw [frob_AH_factor]
  simp only [div_pow, mul_pow]
  ring

/-- `‖A_U‖_F² = v · s_n`. -/
theorem AU_frob (hn : 1 ≤ n) (F : Matrix (Fin n) (Fin n) ℝ) :
    ∑ α, ∑ β, AU F α β ^ 2 = (∑ k, ∑ l, F k l ^ 2) * sN n := by
  rw [frob_AU_factor hn]
  unfold sN Lam
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

end BstLean.Part29
