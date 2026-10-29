import BstLean.Part152SF

/-! Part 244: the smoothed min–max of Gordon's comparison and its derivatives.
For `z : I × J → ℝ`, `G_β(z) = -lse_β(i ↦ -lse_β(j ↦ z (i, j)))` is a soft minimum over rows
of soft maxima over columns. Its gradient is the probability `π = q_i p_{ij}`. -/
namespace BstLean.Part244
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part152 (lse smx sumexp_pos smx_nonneg smx_sum smx_le_one lse_hasDerivAt
  smx_hasDerivAt le_lse lse_le)

section soft

open scoped Classical

variable {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-- The soft maximum of row `i`. -/
noncomputable def rowW (β : ℝ) (z : I × J → ℝ) (i : I) : ℝ := lse β (fun j => z (i, j))

/-- The soft-minimum weights of the rows. -/
noncomputable def qW (β : ℝ) (z : I × J → ℝ) (i : I) : ℝ := smx β (fun i => -rowW β z i) i

/-- The soft-maximum weights inside a row. -/
noncomputable def pW (β : ℝ) (z : I × J → ℝ) (s : I × J) : ℝ := smx β (fun j => z (s.1, j)) s.2

/-- The gradient weights `π_{ij} = q_i p_{ij}`. -/
noncomputable def piW (β : ℝ) (z : I × J → ℝ) (s : I × J) : ℝ := qW β z s.1 * pW β z s

/-- The smoothed min–max. -/
noncomputable def gmm (β : ℝ) (z : I × J → ℝ) : ℝ := -lse β (fun i => -rowW β z i)

/-- The Hessian kernel of the gradient weights (divided by `β`). -/
noncomputable def Tm (β : ℝ) (z : I × J → ℝ) (s s' : I × J) : ℝ :=
  (if s = s' then piW β z s else 0) -
    (if s.1 = s'.1 then 2 * qW β z s.1 * pW β z s * pW β z s' else 0) +
    piW β z s * piW β z s'

lemma qW_nonneg (β : ℝ) (z : I × J → ℝ) (i : I) : 0 ≤ qW β z i := smx_nonneg _ _ _
lemma qW_le_one (β : ℝ) (z : I × J → ℝ) (i : I) : qW β z i ≤ 1 := smx_le_one _ _ _
lemma pW_nonneg (β : ℝ) (z : I × J → ℝ) (s : I × J) : 0 ≤ pW β z s := smx_nonneg _ _ _
lemma pW_le_one (β : ℝ) (z : I × J → ℝ) (s : I × J) : pW β z s ≤ 1 := smx_le_one _ _ _
lemma qW_sum (β : ℝ) (z : I × J → ℝ) : ∑ i, qW β z i = 1 := smx_sum _ _
lemma pW_sum (β : ℝ) (z : I × J → ℝ) (i : I) : ∑ j, pW β z (i, j) = 1 := smx_sum _ _

lemma piW_nonneg (β : ℝ) (z : I × J → ℝ) (s : I × J) : 0 ≤ piW β z s :=
  mul_nonneg (qW_nonneg _ _ _) (pW_nonneg _ _ _)

lemma piW_le_one (β : ℝ) (z : I × J → ℝ) (s : I × J) : piW β z s ≤ 1 :=
  mul_le_one₀ (qW_le_one _ _ _) (pW_nonneg _ _ _) (pW_le_one _ _ _)

lemma piW_sum (β : ℝ) (z : I × J → ℝ) : ∑ s, piW β z s = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [piW, ← Finset.mul_sum, pW_sum, mul_one, qW_sum]

/-- A row-restricted sum over the product index. -/
lemma sum_row (i : I) (f : I × J → ℝ) :
    ∑ s' : I × J, (if i = s'.1 then f s' else 0) = ∑ j, f (i, j) := by
  rw [Fintype.sum_prod_type]
  simp only
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

lemma rowW_hasDerivAt (β : ℝ) (hβ : β ≠ 0) {z : ℝ → I × J → ℝ} {z' : I × J → ℝ} {t : ℝ}
    (hz : ∀ s, HasDerivAt (fun t => z t s) (z' s) t) (i : I) :
    HasDerivAt (fun t => rowW β (z t) i) (∑ j, pW β (z t) (i, j) * z' (i, j)) t := by
  have h := lse_hasDerivAt β (z := fun t j => z t (i, j)) (z' := fun j => z' (i, j)) (t := t)
    (fun j => hz (i, j))
  rw [inv_mul_cancel₀ hβ, one_mul] at h
  exact h

lemma gmm_hasDerivAt (β : ℝ) (hβ : β ≠ 0) {z : ℝ → I × J → ℝ} {z' : I × J → ℝ} {t : ℝ}
    (hz : ∀ s, HasDerivAt (fun t => z t s) (z' s) t) :
    HasDerivAt (fun t => gmm β (z t)) (∑ s, piW β (z t) s * z' s) t := by
  have hw : ∀ i, HasDerivAt (fun t => -rowW β (z t) i)
      (-∑ j, pW β (z t) (i, j) * z' (i, j)) t := fun i => (rowW_hasDerivAt β hβ hz i).neg
  have h := (lse_hasDerivAt β (z := fun t i => -rowW β (z t) i)
    (z' := fun i => -∑ j, pW β (z t) (i, j) * z' (i, j)) (t := t) hw).neg
  rw [inv_mul_cancel₀ hβ, one_mul] at h
  convert h using 1
  · funext t; rfl
  rw [Fintype.sum_prod_type]
  simp only [piW, qW, mul_neg, Finset.sum_neg_distrib, neg_neg, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma piW_hasDerivAt (β : ℝ) (hβ : β ≠ 0) {z : ℝ → I × J → ℝ} {z' : I × J → ℝ} {t : ℝ}
    (hz : ∀ s, HasDerivAt (fun t => z t s) (z' s) t) (s : I × J) :
    HasDerivAt (fun t => piW β (z t) s) (β * ∑ s', Tm β (z t) s s' * z' s') t := by
  obtain ⟨i, j⟩ := s
  have hw : ∀ i, HasDerivAt (fun t => -rowW β (z t) i)
      (-∑ j, pW β (z t) (i, j) * z' (i, j)) t := fun i => (rowW_hasDerivAt β hβ hz i).neg
  have hq := smx_hasDerivAt β (z := fun t i => -rowW β (z t) i)
    (z' := fun i => -∑ j, pW β (z t) (i, j) * z' (i, j)) (t := t) hw i
  have hp := smx_hasDerivAt β (z := fun t j => z t (i, j)) (z' := fun j => z' (i, j)) (t := t)
    (fun j => hz (i, j)) j
  have h := hq.mul hp
  convert h using 1
  · funext t; rfl
  -- the algebra of the Hessian kernel
  have hqq : ∀ l, smx β (fun i => -rowW β (z t) i) l = qW β (z t) l := fun l => rfl
  have hpp : ∀ k, smx β (fun j => z t (i, j)) k = pW β (z t) (i, k) := fun k => rfl
  simp only [hqq, hpp]
  have e1 : ∑ s', (if ((i, j) : I × J) = s' then piW β (z t) (i, j) else 0) * z' s' =
      qW β (z t) i * pW β (z t) (i, j) * z' (i, j) := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, piW]
  have e2 : ∑ s', (if ((i, j) : I × J).1 = s'.1 then
      2 * qW β (z t) ((i, j) : I × J).1 * pW β (z t) (i, j) * pW β (z t) s' else 0) * z' s' =
      2 * qW β (z t) i * pW β (z t) (i, j) * ∑ k, pW β (z t) (i, k) * z' (i, k) := by
    simp only [ite_mul, zero_mul]
    rw [sum_row i (fun s' => 2 * qW β (z t) i * pW β (z t) (i, j) * pW β (z t) s' * z' s')]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e3 : ∑ s', piW β (z t) (i, j) * piW β (z t) s' * z' s' =
      qW β (z t) i * pW β (z t) (i, j) *
        ∑ l, qW β (z t) l * ∑ k, pW β (z t) (l, k) * z' (l, k) := by
    rw [Fintype.sum_prod_type]
    simp only [piW, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  simp only [Tm, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [e1, e2, e3]
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

/-- `Tm` is symmetric. -/
lemma Tm_symm (β : ℝ) (z : I × J → ℝ) (s s' : I × J) : Tm β z s s' = Tm β z s' s := by
  unfold Tm
  by_cases h : s = s'
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    by_cases h1 : s.1 = s'.1
    · rw [if_pos h1, if_pos h1.symm, h1]; ring
    · rw [if_neg h1, if_neg (Ne.symm h1)]; ring

/-- The rows of `Tm` sum to zero. -/
lemma Tm_row (β : ℝ) (z : I × J → ℝ) (s : I × J) : ∑ s', Tm β z s s' = 0 := by
  unfold Tm
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, ← Finset.mul_sum,
    piW_sum]
  rw [sum_row s.1 (fun s' => 2 * qW β z s.1 * pW β z s * pW β z s')]
  simp only [← Finset.mul_sum, pW_sum, if_pos (Finset.mem_univ _), piW]
  ring

/-- Off-diagonal signs of `Tm`. -/
lemma Tm_same_row (β : ℝ) (z : I × J → ℝ) {s s' : I × J} (hne : s ≠ s') (h1 : s.1 = s'.1) :
    Tm β z s s' ≤ 0 := by
  unfold Tm
  rw [if_neg hne, if_pos h1]
  simp only [piW, ← h1]
  have hq0 := qW_nonneg β z s.1
  have hq1 := qW_le_one β z s.1
  have hpp := mul_nonneg (pW_nonneg β z s) (pW_nonneg β z s')
  nlinarith [mul_nonneg hq0 hpp, mul_nonneg (mul_nonneg hq0 hq0) hpp]

lemma Tm_cross_row (β : ℝ) (z : I × J → ℝ) {s s' : I × J} (h1 : s.1 ≠ s'.1) :
    0 ≤ Tm β z s s' := by
  have hne : s ≠ s' := fun h => h1 (by rw [h])
  unfold Tm
  rw [if_neg hne, if_neg h1]
  have := mul_nonneg (piW_nonneg β z s) (piW_nonneg β z s')
  linarith

lemma abs_Tm_le (β : ℝ) (z : I × J → ℝ) (s s' : I × J) : |Tm β z s s'| ≤ 4 := by
  unfold Tm
  have h0 := piW_nonneg β z s
  have h1 := piW_le_one β z s
  have h2 := piW_nonneg β z s'
  have h3 := piW_le_one β z s'
  have hq0 := qW_nonneg β z s.1
  have hq1 := qW_le_one β z s.1
  have hp0 := pW_nonneg β z s
  have hp1 := pW_le_one β z s
  have hp0' := pW_nonneg β z s'
  have hp1' := pW_le_one β z s'
  have hA : 0 ≤ (if s = s' then piW β z s else 0) ∧ (if s = s' then piW β z s else 0) ≤ 1 := by
    split_ifs <;> constructor <;> linarith
  have hqp : 0 ≤ qW β z s.1 * pW β z s * pW β z s' := by positivity
  have hqp1 : qW β z s.1 * pW β z s * pW β z s' ≤ 1 := by
    have := mul_le_one₀ hq1 hp0 hp1
    exact mul_le_one₀ this hp0' hp1'
  have hB : 0 ≤ (if s.1 = s'.1 then 2 * qW β z s.1 * pW β z s * pW β z s' else 0) ∧
      (if s.1 = s'.1 then 2 * qW β z s.1 * pW β z s * pW β z s' else 0) ≤ 2 := by
    split_ifs <;> constructor <;> nlinarith
  have hC : 0 ≤ piW β z s * piW β z s' := mul_nonneg h0 h2
  have hC1 : piW β z s * piW β z s' ≤ 1 := mul_le_one₀ h1 h2 h3
  rw [abs_le]
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]

/-- **The sign lemma.** A symmetric kernel with zero row sums whose entries have the signs of the
increment differences gives a nonpositive quadratic form. -/
lemma quad_nonpos {S : Type} [Fintype S] (T Δ : S → S → ℝ) (hsym : ∀ s s', T s s' = T s' s)
    (hrow : ∀ s, ∑ s', T s s' = 0)
    (hsign : ∀ s s', 0 ≤ T s s' * (Δ s s + Δ s' s' - 2 * Δ s s')) :
    ∑ s, ∑ s', T s s' * Δ s s' ≤ 0 := by
  have h1 : ∑ s, ∑ s', T s s' * Δ s s = 0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← Finset.sum_mul, hrow, zero_mul]
  have h2 : ∑ s, ∑ s', T s s' * Δ s' s' = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun s' _ => ?_
    have : ∑ s, T s s' * Δ s' s' = (∑ s, T s' s) * Δ s' s' := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s _ => by rw [hsym]
    rw [this, hrow, zero_mul]
  have h3 : 0 ≤ ∑ s, ∑ s', T s s' * (Δ s s + Δ s' s' - 2 * Δ s s') :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun s' _ => hsign s s'
  have e : ∑ s, ∑ s', T s s' * (Δ s s + Δ s' s' - 2 * Δ s s') =
      ∑ s, ∑ s', T s s' * Δ s s + ∑ s, ∑ s', T s s' * Δ s' s' -
        2 * ∑ s, ∑ s', T s s' * Δ s s' := by
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring
  rw [e, h1, h2] at h3
  linarith

/-- Bounds of the smoothed min–max by the min–max. -/
noncomputable def minmax (z : I × J → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => Finset.univ.sup' Finset.univ_nonempty
    (fun j => z (i, j)))

lemma gmm_le {β : ℝ} (hβ : 0 < β) (z : I × J → ℝ) :
    gmm β z ≤ minmax z + Real.log (Fintype.card J) / β := by
  unfold minmax
  rw [← sub_le_iff_le_add]
  refine Finset.le_inf' _ _ fun i _ => ?_
  rw [sub_le_iff_le_add]
  have h1 : -rowW β z i ≤ lse β (fun i => -rowW β z i) := le_lse hβ (fun i => -rowW β z i) i
  have h2 : rowW β z i ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => z (i, j)) +
      Real.log (Fintype.card J) / β :=
    lse_le hβ fun j => Finset.le_sup' (fun j => z (i, j)) (Finset.mem_univ j)
  unfold gmm
  linarith

lemma le_gmm {β : ℝ} (hβ : 0 < β) (z : I × J → ℝ) :
    minmax z - Real.log (Fintype.card I) / β ≤ gmm β z := by
  have h : lse β (fun i => -rowW β z i) ≤ -minmax z + Real.log (Fintype.card I) / β := by
    refine lse_le hβ fun i => ?_
    have h1 : minmax z ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => z (i, j)) :=
      Finset.inf'_le _ (Finset.mem_univ i)
    obtain ⟨j0⟩ := ‹Nonempty J›
    have h2 : Finset.univ.sup' Finset.univ_nonempty (fun j => z (i, j)) ≤ rowW β z i :=
      Finset.sup'_le _ _ fun j _ => le_lse hβ (fun j => z (i, j)) j
    linarith
  unfold gmm
  linarith

end soft

end BstLean.Part244
