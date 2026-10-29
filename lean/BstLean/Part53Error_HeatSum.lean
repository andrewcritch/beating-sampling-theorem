import BstLean.Part53Error_Heat

namespace BstLean.Part53

/-- Reindex the triangular range of two heat depths by their total depth. -/
theorem error53_heat_triangle_sum (k c : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
      ∑ j ∈ (Finset.range (k + 1)).filter (fun j => c + 2 * i + 2 * j ≤ k), F i j) =
    ∑ l ∈ (Finset.range (k + 1)).filter (fun l => c + 2 * l ≤ k),
      ∑ i ∈ Finset.range (l + 1), F i (l - i) := by
  classical
  let P := (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))
  let S := P.filter (fun p => c + 2 * (p.1 + p.2) ≤ k)
  let T := P.filter (fun p => c + 2 * p.1 ≤ k ∧ p.2 ≤ p.1)
  have hleft : (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
      ∑ j ∈ (Finset.range (k + 1)).filter (fun j => c + 2 * i + 2 * j ≤ k), F i j) =
      ∑ p ∈ S, F p.1 p.2 := by
    simp only [S, P, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : c + 2 * i ≤ k
    · simp only [hi, ite_true]
      apply Finset.sum_congr rfl
      intro j _
      rw [show c + 2 * i + 2 * j = c + 2 * (i + j) by omega]
    · simp only [hi, ite_false]
      symm
      apply Finset.sum_eq_zero
      intro j _
      have hj : ¬ c + 2 * (i + j) ≤ k := by omega
      simp [hj]
  have hright : (∑ p ∈ T, F p.2 (p.1 - p.2)) =
      ∑ l ∈ (Finset.range (k + 1)).filter (fun l => c + 2 * l ≤ k),
        ∑ i ∈ Finset.range (l + 1), F i (l - i) := by
    simp only [T, P, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro l hl
    have hlk : l ≤ k := by have := Finset.mem_range.mp hl; omega
    by_cases hcl : c + 2 * l ≤ k
    · simp only [hcl, true_and, ite_true]
      have hf : (Finset.range (k + 1)).filter (fun i => i ≤ l) = Finset.range (l + 1) := by
        ext i
        simp
        omega
      rw [← Finset.sum_filter, hf]
    · simp [hcl]
  rw [hleft, ← hright]
  apply Finset.sum_bij (fun p _ => (p.1 + p.2, p.1))
  · intro p hp
    simp only [S, P, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [T, P, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  · intro p hp q hq heq
    apply Prod.ext
    · exact (Prod.mk.inj heq).2
    · have h1 := (Prod.mk.inj heq).1
      have h2 := (Prod.mk.inj heq).2
      omega
  · intro q hq
    simp only [T, P, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    refine ⟨(q.2, q.1 - q.2), ?_, ?_⟩
    · simp only [S, P, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · apply Prod.ext <;> simp only <;> omega
  · intro p hp
    simp

private noncomputable def heatCoeff (v : ℝ) (c i : ℕ) : ℝ :=
  (v / 2) ^ i / (i.factorial : ℝ) *
    (((c + 2 * i).factorial : ℝ) / (c.factorial : ℝ))

private lemma heatCoeff_convolution (v b : ℝ) (c l : ℕ) :
    (∑ i ∈ Finset.range (l + 1), heatCoeff v c i * heatCoeff b (c + 2 * i) (l - i)) =
      heatCoeff (v + b) c l := by
  calc
    _ = ∑ i ∈ Finset.range (l + 1),
        ((v / 2) ^ i / (i.factorial : ℝ) *
          ((b / 2) ^ (l - i) / ((l - i).factorial : ℝ))) *
            (((c + 2 * l).factorial : ℝ) / (c.factorial : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hil : i ≤ l := by have := Finset.mem_range.mp hi; omega
      have heq : c + 2 * i + 2 * (l - i) = c + 2 * l := by omega
      unfold heatCoeff
      rw [heq]
      field_simp <;> ring
    _ = heatCoeff (v + b) c l := by
      rw [← Finset.sum_mul, error53_heat_weight_convolution]
      rfl

private lemma heat_formula {n : ℕ} (k : ℕ) (v : ℝ) (A : BstLean.Part41.Tens n)
    (c : ℕ) (w : Fin c → Fin n) :
    heatA k v A c w = ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
      heatCoeff v c i * error53_traceCoeff A c i w := rfl

private lemma trace_heat_formula {n : ℕ} (k : ℕ) (b : ℝ) (A : BstLean.Part41.Tens n)
    (c i : ℕ) (w : Fin c → Fin n) :
    error53_traceCoeff (heatA k b A) c i w =
      ∑ j ∈ (Finset.range (k + 1)).filter (fun j => c + 2 * i + 2 * j ≤ k),
        heatCoeff b (c + 2 * i) j * error53_traceCoeff A c (i + j) w := by
  classical
  conv_lhs => unfold error53_traceCoeff BstLean.Part41.trL
  simp_rw [heat_formula]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum]
  congr 1
  change error53_traceCoeff (fun a => error53_traceCoeff A a j) c i w =
    error53_traceCoeff A c (i + j) w
  exact congrFun (error53_traceCoeff_comp A c i j) w

/-- The frozen finite heat operator satisfies the semigroup identity at every real time. -/
theorem error53_heat_add {n : ℕ} (k : ℕ) (v b : ℝ) (A : BstLean.Part41.Tens n) :
    heatA k v (heatA k b A) = heatA k (v + b) A := by
  classical
  funext c w
  simp_rw [heat_formula, trace_heat_formula, Finset.mul_sum]
  rw [error53_heat_triangle_sum]
  apply Finset.sum_congr rfl
  intro l hl
  calc
    _ = (∑ i ∈ Finset.range (l + 1),
        heatCoeff v c i * heatCoeff b (c + 2 * i) (l - i)) * error53_traceCoeff A c l w := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have heq : i + (l - i) = l := by have := Finset.mem_range.mp hi; omega
      rw [heq]
      ring
    _ = _ := by rw [heatCoeff_convolution]

end BstLean.Part53
