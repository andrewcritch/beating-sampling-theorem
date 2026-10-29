import Mathlib

/-!
# Part 29, layer L2: the exact formula for `B` at `(2,2)`

`proofs/option-m/19-quadratic-quadratic-boundary.tex`, the obstruction formula, used by part 29's exact
branch. For `m(x)_k = c_k + (L x)_k + xᵀ Q_k x` (each `Q_k` symmetric) and
`f(y) = f₀ + gᵀ y + yᵀ F y` (`F` symmetric), and a law with the uniform-sphere moments up to degree
four (taken as hypotheses), `B = ∫ f(m(x))` is an explicit polynomial in the coefficients.
-/

namespace BstLean.Part29

open MeasureTheory

variable {n : ℕ}

/-- The uniform-sphere moments up to degree four, with integrability, taken as hypotheses. -/
structure SphereMoments (n : ℕ) (μ : Measure (Fin n → ℝ)) : Prop where
  int1 : ∀ i, Integrable (fun x : Fin n → ℝ => x i) μ
  int2 : ∀ i j, Integrable (fun x : Fin n → ℝ => x i * x j) μ
  int3 : ∀ i j k, Integrable (fun x : Fin n → ℝ => x i * x j * x k) μ
  int4 : ∀ i j k l, Integrable (fun x : Fin n → ℝ => x i * x j * x k * x l) μ
  m1 : ∀ i, ∫ x, x i ∂μ = 0
  m2 : ∀ i j, ∫ x, x i * x j ∂μ = if i = j then 1 / (n : ℝ) else 0
  m3 : ∀ i j k, ∫ x, x i * x j * x k ∂μ = 0
  m4 : ∀ i j k l, ∫ x, x i * x j * x k * x l ∂μ =
    ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0)) / ((n : ℝ) * (n + 2))

/-- The quadratic map `m`. -/
def mapM (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  c k + ∑ i, L k i * x i + ∑ i, ∑ j, Q k i j * x i * x j

/-- The quadratic function `f`. -/
def funF (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) : ℝ :=
  f0 + ∑ k, g k * y k + ∑ k, ∑ l, F k l * y k * y l

local notation "lin" => (fun (a : Fin n → ℝ) (x : Fin n → ℝ) => ∑ i, a i * x i)
local notation "quad" => (fun (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) =>
  ∑ i, ∑ j, A i j * (x i * x j))

private lemma integrable_lin (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (a : Fin n → ℝ) : Integrable (lin a) μ :=
  integrable_finsetSum _ (fun i _ => (h.int1 i).const_mul (a i))

private lemma integrable_quad (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Integrable (quad A) μ :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (h.int2 i j).const_mul (A i j)))

private lemma integrable_ll (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (a b : Fin n → ℝ) : Integrable (fun x => lin a x * lin b x) μ := by
  dsimp only
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  convert (h.int2 i j).const_mul (a i * b j) using 1
  funext x
  ring

private lemma integrable_lq (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (a : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => lin a x * quad A x) μ := by
  dsimp only
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  convert (h.int3 i j k).const_mul (a i * A j k) using 1
  funext x
  ring

private lemma integrable_qq (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => quad A x * quad B x) μ := by
  dsimp only
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro l _
  convert (h.int4 i j k l).const_mul (A i j * B k l) using 1
  funext x
  ring

private lemma int_lin (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (a : Fin n → ℝ) : ∫ x, lin a x ∂μ = 0 := by
  dsimp only
  rw [integral_finsetSum _ (fun i _ => (h.int1 i).const_mul (a i))]
  simp [integral_const_mul, h.m1]

private lemma int_quad (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∫ x, quad A x ∂μ = (∑ i, A i i) / n := by
  dsimp only
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (h.int2 i j).const_mul (A i j)))]
  simp_rw [integral_finsetSum _ (fun j _ => (h.int2 _ j).const_mul (A _ j)),
    integral_const_mul, h.m2]
  simp [mul_ite, div_eq_mul_inv, Finset.sum_mul]

private lemma int_ll (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (a b : Fin n → ℝ) :
    ∫ x, lin a x * lin b x ∂μ = (∑ i, a i * b i) / n := by
  have expand (x : Fin n → ℝ) : lin a x * lin b x =
      ∑ i, ∑ j, (a i * b j) * (x i * x j) := by
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [expand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (h.int2 i j).const_mul (a i * b j)))]
  simp_rw [integral_finsetSum _ (fun j _ => (h.int2 _ j).const_mul _),
    integral_const_mul, h.m2]
  simp [mul_ite, div_eq_mul_inv, Finset.sum_mul]

private lemma int_lq (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (a : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∫ x, lin a x * quad A x ∂μ = 0 := by
  have expand (x : Fin n → ℝ) : lin a x * quad A x =
      ∑ i, ∑ j, ∑ k, (a i * A j k) * (x i * x j * x k) := by
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [expand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => integrable_finsetSum _ (fun k _ =>
      (h.int3 i j k).const_mul (a i * A j k))))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun k _ => (h.int3 _ j k).const_mul _)),
    integral_finsetSum _ (fun k _ => (h.int3 _ _ k).const_mul _),
    integral_const_mul, h.m3]
  simp

private lemma int_qq (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (A B : Fin n → Fin n → ℝ) (hB : Matrix.IsSymm B) :
    ∫ x, quad A x * quad B x ∂μ =
      ((∑ i, A i i) * (∑ j, B j j) + 2 * ∑ i, ∑ j, A i j * B j i) /
        ((n : ℝ) * (n + 2)) := by
  have expand (x : Fin n → ℝ) : quad A x * quad B x =
      ∑ i, ∑ j, ∑ k, ∑ l, (A i j * B k l) * (x i * x j * x k * x l) := by
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [expand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _
      (fun l _ => (h.int4 i j k l).const_mul (A i j * B k l)))))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun k _ => integrable_finsetSum _ (fun l _ => (h.int4 _ j k l).const_mul _))),
    integral_finsetSum _ (fun k _ => integrable_finsetSum _
      (fun l _ => (h.int4 _ _ k l).const_mul _)),
    integral_finsetSum _ (fun l _ => (h.int4 _ _ _ l).const_mul _),
    integral_const_mul, h.m4]
  simp only [← mul_div_assoc, ← Finset.sum_div]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [ite_and, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [hB.apply]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

private lemma mapM_eq (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (k : Fin n) :
    mapM c L Q x k = c k + lin (L k) x + quad (Q k) x := by
  simp only [mapM, mul_assoc]

private lemma integrable_map (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h : SphereMoments n μ) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Integrable (fun x => mapM c L Q x k) μ := by
  simp_rw [mapM_eq]
  exact ((integrable_const _).add (integrable_lin μ h _)).add (integrable_quad μ h _)

private lemma int_map (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h : SphereMoments n μ) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    ∫ x, mapM c L Q x k ∂μ = c k + (∑ i, Q k i i) / n := by
  simp_rw [mapM_eq]
  rw [integral_add (f := fun x => c k + lin (L k) x) (g := fun x => quad (Q k) x)
    ((integrable_const (c k)).add (integrable_lin μ h (L k)))
    (integrable_quad μ h (Q k)), integral_add (integrable_const (c k)) (integrable_lin μ h (L k))]
  simp [int_lin, int_quad, h]

private lemma integrable_pair (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h : SphereMoments n μ) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (k l : Fin n) :
    Integrable (fun x => mapM c L Q x k * mapM c L Q x l) μ := by
  have hlk := integrable_lin μ h (L k)
  have hll := integrable_lin μ h (L l)
  have hqk := integrable_quad μ h (Q k)
  have hql := integrable_quad μ h (Q l)
  have hll' := integrable_ll μ h (L k) (L l)
  have hlq := integrable_lq μ h (L k) (Q l)
  have hql' : Integrable (fun x => quad (Q k) x * lin (L l) x) μ := by
    simpa only [mul_comm] using integrable_lq μ h (L l) (Q k)
  have hqq := integrable_qq μ h (Q k) (Q l)
  simp only [mapM_eq, add_mul, mul_add]
  fun_prop

private lemma int_pair (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h : SphereMoments n μ) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ k, (Q k).IsSymm)
    (k l : Fin n) :
    ∫ x, mapM c L Q x k * mapM c L Q x l ∂μ =
      c k * c l + c k * ((∑ i, Q l i i) / n) + ((∑ i, Q k i i) / n) * c l
      + (∑ i, L k i * L l i) / n
      + ((∑ i, Q k i i) * (∑ j, Q l j j) + 2 * ∑ i, ∑ j, Q k i j * Q l j i) /
        ((n : ℝ) * (n + 2)) := by
  have hlk := integrable_lin μ h (L k)
  have hll := integrable_lin μ h (L l)
  have hqk := integrable_quad μ h (Q k)
  have hql := integrable_quad μ h (Q l)
  have hll' := integrable_ll μ h (L k) (L l)
  have hlq := integrable_lq μ h (L k) (Q l)
  have hql' : Integrable (fun x => quad (Q k) x * lin (L l) x) μ := by
    simpa only [mul_comm] using integrable_lq μ h (L l) (Q k)
  have hqq := integrable_qq μ h (Q k) (Q l)
  simp only [mapM_eq, add_mul, mul_add]
  simp (disch := fun_prop) only [integral_add]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_const_mul, integral_mul_const, int_lin μ h, int_quad μ h,
    int_ll μ h, int_lq μ h]
  have hz : (∫ x, quad (Q k) x * lin (L l) x ∂μ) = 0 := by
    simpa only [mul_comm] using int_lq μ h (L l) (Q k)
  rw [hz]
  have hv := int_qq μ h (Q k) (Q l) (hQ l)
  dsimp only at hv
  rw [hv]
  ring

/-- **The exact formula.** With `t_k = tr Q_k`, `ν_k = c_k + t_k / n` and `K_kl = tr(Q_k Q_l)`:
`B = f₀ + gᵀν + νᵀFν + ⟨F, L Lᵀ⟩/n + 2/(n(n+2)) · (⟨F, K⟩ − tᵀ F t / n)`. -/
theorem exact_formula (hn : 1 ≤ n) (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : SphereMoments n μ)
    (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ k, (Q k).IsSymm) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) :
    let t : Fin n → ℝ := fun k => ∑ i, Q k i i
    let ν : Fin n → ℝ := fun k => c k + t k / n
    let K : Fin n → Fin n → ℝ := fun k l => ∑ i, ∑ j, Q k i j * Q l j i
    ∫ x, funF f0 g F (mapM c L Q x) ∂μ =
      f0 + ∑ k, g k * ν k + ∑ k, ∑ l, F k l * ν k * ν l
        + (∑ k, ∑ l, F k l * ∑ i, L k i * L l i) / n
        + 2 / ((n : ℝ) * (n + 2)) * (∑ k, ∑ l, F k l * K k l - (∑ k, ∑ l, F k l * t k * t l) / n) := by
  dsimp only
  let t : Fin n → ℝ := fun k => ∑ i, Q k i i
  let ν : Fin n → ℝ := fun k => c k + t k / n
  let K : Fin n → Fin n → ℝ := fun k l => ∑ i, ∑ j, Q k i j * Q l j i
  change (∫ x, funF f0 g F (mapM c L Q x) ∂μ) =
    f0 + ∑ k, g k * ν k + ∑ k, ∑ l, F k l * ν k * ν l
      + (∑ k, ∑ l, F k l * ∑ i, L k i * L l i) / n
      + 2 / ((n : ℝ) * (n + 2)) *
        (∑ k, ∑ l, F k l * K k l - (∑ k, ∑ l, F k l * t k * t l) / n)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have hm (k : Fin n) : (∫ x, mapM c L Q x k ∂μ) = ν k := int_map μ hμ c L Q k
  have hp (k l : Fin n) : (∫ x, mapM c L Q x k * mapM c L Q x l ∂μ) =
      ν k * ν l + (∑ i, L k i * L l i) / n
        + 2 / ((n : ℝ) * (n + 2)) * (K k l - t k * t l / n) := by
    rw [int_pair μ hμ c L Q hQ]
    dsimp [ν, t, K]
    field_simp [hn0, hn2]
    ring
  have hi (k : Fin n) := (integrable_map μ hμ c L Q k).const_mul (g k)
  have hij (k l : Fin n) :
      Integrable (fun x => F k l * mapM c L Q x k * mapM c L Q x l) μ := by
    simpa only [mul_assoc] using (integrable_pair μ hμ c L Q k l).const_mul (F k l)
  simp only [funF]
  rw [integral_add (f := fun x => f0 + ∑ k, g k * mapM c L Q x k)
      (g := fun x => ∑ k, ∑ l, F k l * mapM c L Q x k * mapM c L Q x l)
      ((integrable_const f0).add (integrable_finsetSum Finset.univ (fun k _ => hi k)))
      (integrable_finsetSum Finset.univ
        (fun k _ => integrable_finsetSum Finset.univ (fun l _ => hij k l))),
    integral_add (integrable_const f0) (integrable_finsetSum Finset.univ (fun k _ => hi k)),
    integral_finsetSum _ (fun k _ => hi k),
    integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hij k l))]
  simp_rw [integral_finsetSum _ (fun l _ => hij _ l)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_const_mul, mul_assoc, hm, hp]
  have term (k l : Fin n) :
      F k l * (ν k * ν l + (∑ i, L k i * L l i) / n +
        2 / ((n : ℝ) * (n + 2)) * (K k l - t k * t l / n)) =
      F k l * ν k * ν l + (F k l * ∑ i, L k i * L l i) / n +
        2 / ((n : ℝ) * (n + 2)) * (F k l * K k l - F k l * t k * t l / n) := by ring
  simp_rw [term]
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
    Finset.sum_sub_distrib]
  ring

end BstLean.Part29
