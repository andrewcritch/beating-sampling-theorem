import BstLean.Part53Defs
import BstLean.Part41Tensor

namespace BstLean.Part53
open BstLean.Part41 (Tens trL glue IsSymmT)
private lemma error53_append_val {ι : Type*} {l i : ℕ} (c : Fin l → ι) (c' : Fin i → ι)
    (u : Fin (l + i)) :
    Fin.append c c' u = if h : u.1 < l then c ⟨u.1, h⟩ else c' ⟨u.1 - l, by omega⟩ := by
  split_ifs with h
  · have : u = Fin.castAdd i ⟨u.1, h⟩ := Fin.ext rfl
    exact (congrArg (Fin.append c c') this).trans (Fin.append_left c c' _)
  · have : u = Fin.natAdd l ⟨u.1 - l, by omega⟩ := Fin.ext (by simp; omega)
    exact (congrArg (Fin.append c c') this).trans (Fin.append_right c c' _)

private lemma error53_glue_glue {ι : Type*} (j l i : ℕ) (hj : 2 * (l + i) ≤ j)
    (c : Fin l → ι) (c' : Fin i → ι) (w : Fin (j - 2 * l - 2 * i) → ι) :
    glue j l c (glue (j - 2 * l) i c' w) =
      glue j (l + i) (Fin.append c c') (fun t => w ⟨t.1, by have := t.2; omega⟩) := by
  funext t
  unfold glue
  simp only [error53_append_val]
  split_ifs <;> first
    | rfl
    | (congr 1; apply Fin.ext; simp only; omega)
    | omega

theorem error53_trace_comp {ι R : Type*} [Fintype ι] [AddCommMonoid R] {j : ℕ} (l i : ℕ)
    (hj : 2 * (l + i) ≤ j) (A : (Fin j → ι) → R) (w : Fin (j - 2 * l - 2 * i) → ι) :
    trL i (trL l A) w = trL (l + i) A (fun t => w ⟨t.1, by have := t.2; omega⟩) := by
  classical
  unfold trL
  rw [Finset.sum_comm]
  simp_rw [error53_glue_glue j l i hj]
  rw [← (Fin.appendEquiv l i).sum_comp, Fintype.sum_prod_type]
  rfl


private lemma trace_zero {ι : Type*} [Fintype ι] {j : ℕ}
    (A : (Fin j → ι) → ℝ) : trL 0 A = A := by
  classical
  funext w
  simp only [trL, Finset.univ_unique, Finset.sum_singleton]
  congr 1

/-- Zero heat time gives the original coefficient at every retained order. -/
theorem error53_heat_zero {n : ℕ} (k c : ℕ) (hc : c ≤ k) (A : Tens n) :
    heatA k 0 A c = A c := by
  classical
  funext w
  unfold heatA
  rw [Finset.sum_eq_single 0]
  · simp only [mul_zero, add_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, zero_div]
    rw [div_self (by positivity : (c.factorial : ℝ) ≠ 0), one_mul, trace_zero]
    simp only [mul_zero, add_zero, one_mul]
    rfl
  · intro i hi hi0
    simp [zero_pow hi0]
  · intro h0
    exact False.elim (h0 (by simp [hc]))

/-- Every heat coefficient above the degree cutoff vanishes. -/
theorem error53_heat_above {n : ℕ} (k c : ℕ) (hc : k < c) (v : ℝ) (A : Tens n) :
    heatA k v A c = 0 := by
  funext w
  have hf : (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k) = ∅ := by
    ext i
    simp
    omega
  simp [heatA, hf]

/-- The heat family retains tensor symmetry. -/
theorem error53_heat_symm {n k : ℕ} (v : ℝ) (A : Tens n)
    (hA : ∀ j, IsSymmT (A j)) : ∀ c, IsSymmT (heatA k v A c) := by
  classical
  intro c σ w
  unfold heatA
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have hdim : c + 2 * i - 2 * i = c := by omega
  let e : Fin (c + 2 * i - 2 * i) ≃ Fin c := finCongr hdim
  let τ := e.trans (σ.trans e.symm)
  have he : (fun t : Fin (c + 2 * i - 2 * i) => (w ∘ σ) ⟨t.1, by omega⟩) =
      (fun t : Fin (c + 2 * i - 2 * i) => w ⟨t.1, by omega⟩) ∘ τ := by
    funext t
    rfl
  rw [he]
  exact BstLean.Part41.trL_symm i (by omega) _ (hA _) τ _

/-- The exponential heat weights satisfy the binomial convolution identity. -/
theorem error53_heat_weight_convolution (v b : ℝ) (l : ℕ) :
    (∑ i ∈ Finset.range (l + 1),
      (v / 2) ^ i / (i.factorial : ℝ) *
        ((b / 2) ^ (l - i) / ((l - i).factorial : ℝ))) =
      ((v + b) / 2) ^ l / (l.factorial : ℝ) := by
  rw [show (v + b) / 2 = v / 2 + b / 2 by ring, add_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i ≤ l := by have := Finset.mem_range.mp hi; omega
  have hfac : (l.choose i : ℝ) * (i.factorial : ℝ) * ((l - i).factorial : ℝ) =
      (l.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hil
  have hi0 : (i.factorial : ℝ) ≠ 0 := by positivity
  have hj0 : ((l - i).factorial : ℝ) ≠ 0 := by positivity
  have hl0 : (l.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  rw [← hfac]
  ring

/-- An iterated trace with the free slots indexed by the requested tensor order. -/
noncomputable def error53_traceCoeff {n : ℕ} (A : Tens n) (c i : ℕ) :
    (Fin c → Fin n) → ℝ := fun w =>
  trL i (A (c + 2 * i)) (fun t => w ⟨t.1, by have := t.2; omega⟩)

/-- The canonical trace coefficients compose by addition of their depths. -/
private lemma tensor_order_cast {n a b : ℕ} (h : a = b) (A : Tens n)
    (w : Fin a → Fin n) : A a w = A b (fun t => w ⟨t.1, by have := t.2; omega⟩) := by
  subst b
  rfl

theorem error53_traceCoeff_comp {n : ℕ} (A : Tens n) (c i j : ℕ) :
    error53_traceCoeff (fun a => error53_traceCoeff A a j) c i =
      error53_traceCoeff A c (i + j) := by
  classical
  funext w
  conv_rhs => rw [Nat.add_comm i j]
  simp only [error53_traceCoeff, trL]
  rw [Finset.sum_comm]
  rw [← (Fin.appendEquiv j i).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro qj _
  apply Finset.sum_congr rfl
  intro qi _
  rw [tensor_order_cast (show c + 2 * i + 2 * j = c + 2 * (j + i) by omega) A]
  congr 1
  funext t
  dsimp only [Fin.appendEquiv]
  simp only [Equiv.coe_fn_mk]
  unfold glue
  simp only [error53_append_val]
  split_ifs <;> first
    | rfl
    | (congr 1; apply Fin.ext; simp only; omega)
    | omega

end BstLean.Part53
