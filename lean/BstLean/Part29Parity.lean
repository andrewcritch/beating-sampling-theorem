import BstLean.Part29ExactFormula

/-!
# Part 29, layer L4 (F2): parity identifies the four-index coefficient

For a law with sphere parity (a product of at most eight coordinates integrates to zero unless every index
appears an even number of times) and `E x_S² = w` for distinct four-sets, the projection of `f(m(x))` on the
multilinear monomial `x_S = x_{σ0} x_{σ1} x_{σ2} x_{σ3}` receives only the product of the quadratic parts
of `m`: `E[f(m(x)) x_S] = w · C_σ`, with `C_σ` the sum over the 24 orderings of `S`.
-/

namespace BstLean.Part29

open MeasureTheory

variable {n : ℕ}

/-- Sphere parity up to degree eight, the value of `E x_S²`, and integrability. -/
structure SphereParity (n : ℕ) (μ : Measure (Fin n → ℝ)) (w : ℝ) : Prop where
  integ : ∀ (r : ℕ), r ≤ 8 → ∀ τ : Fin r → Fin n,
    Integrable (fun x : Fin n → ℝ => ∏ s, x (τ s)) μ
  parity : ∀ (r : ℕ), r ≤ 8 → ∀ τ : Fin r → Fin n,
    (∃ i, Odd (Finset.univ.filter (fun s => τ s = i)).card) → ∫ x, ∏ s, x (τ s) ∂μ = 0
  square : ∀ σ : Fin 4 → Fin n, Function.Injective σ → ∫ x, ∏ s, x (σ s) ^ 2 ∂μ = w

/-- The four-index coefficient: `Σ_{k,l} F_kl Σ_π Q_k(σπ0, σπ1) Q_l(σπ2, σπ3)` over the orderings `π`. -/
noncomputable def coeffS (F : Matrix (Fin n) (Fin n) ℝ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (σ : Fin 4 → Fin n) : ℝ :=
  ∑ k, ∑ l, F k l * ∑ π : Equiv.Perm (Fin 4),
    Q k (σ (π 0)) (σ (π 1)) * Q l (σ (π 2)) (σ (π 3))

private lemma prod_append {r : ℕ} (τ : Fin r → Fin n) (σ : Fin 4 → Fin n)
    (x : Fin n → ℝ) :
    (∏ s, x (Fin.append τ σ s)) = (∏ s, x (τ s)) * ∏ s, x (σ s) := by
  rw [Fin.prod_univ_add]
  simp

private lemma integ_prod (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) {r : ℕ} (hr : r ≤ 4)
    (τ : Fin r → Fin n) (σ : Fin 4 → Fin n) :
    Integrable (fun x => (∏ s, x (τ s)) * ∏ s, x (σ s)) μ := by
  simpa only [prod_append] using hμ.integ (r + 4) (by omega) (Fin.append τ σ)

private lemma int_missing (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) {r : ℕ} (hr : r ≤ 4)
    (τ : Fin r → Fin n) (σ : Fin 4 → Fin n) (hσ : Function.Injective σ)
    (s : Fin 4) (hs : ∀ t, τ t ≠ σ s) :
    (∫ x, (∏ t, x (τ t)) * ∏ t, x (σ t) ∂μ) = 0 := by
  have hc : (Finset.univ.filter (fun t => Fin.append τ σ t = σ s)).card = 1 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    simp [hs, hσ.eq_iff]
  simpa only [prod_append] using hμ.parity (r + 4) (by omega) (Fin.append τ σ)
    ⟨σ s, by rw [hc]; decide⟩

private lemma int_short (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) {r : ℕ} (hr : r < 4)
    (τ : Fin r → Fin n) (σ : Fin 4 → Fin n) (hσ : Function.Injective σ) :
    (∫ x, (∏ t, x (τ t)) * ∏ t, x (σ t) ∂μ) = 0 := by
  classical
  have hm : ∃ s, ∀ t, τ t ≠ σ s := by
    by_contra h
    push Not at h
    choose a ha using h
    have hinj : Function.Injective a := by
      intro s t he
      apply hσ
      rw [← ha s, ← ha t, he]
    have hc := Fintype.card_le_of_injective a hinj
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨s, hs⟩ := hm
  exact int_missing μ w hμ (by omega) τ σ hσ s hs

private lemma four_coverage (τ σ : Fin 4 → Fin n) (hσ : Function.Injective σ) :
    (∀ s, ∃ t, τ t = σ s) ↔ ∃ π : Equiv.Perm (Fin 4), τ = σ ∘ π := by
  classical
  constructor
  · intro h
    choose a ha using h
    have hinj : Function.Injective a := by
      intro s t he
      apply hσ
      rw [← ha s, ← ha t, he]
    let e : Equiv.Perm (Fin 4) := Equiv.ofBijective a
      ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩
    refine ⟨e.symm, ?_⟩
    funext t
    have hv := ha (e.symm t)
    change τ (e (e.symm t)) = σ (e.symm t) at hv
    simpa using hv
  · rintro ⟨π, rfl⟩ s
    exact ⟨π.symm s, by simp⟩

private lemma int_four (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (τ σ : Fin 4 → Fin n) (hσ : Function.Injective σ) :
    (∫ x, (∏ t, x (τ t)) * ∏ t, x (σ t) ∂μ) =
      if ∃ π : Equiv.Perm (Fin 4), τ = σ ∘ π then w else 0 := by
  classical
  split_ifs with h
  · obtain ⟨π, rfl⟩ := h
    have hp (x : Fin n → ℝ) : (∏ t, x ((σ ∘ π) t)) = ∏ t, x (σ t) := by
      exact Equiv.prod_comp π (fun t => x (σ t))
    simp_rw [hp, ← Finset.prod_mul_distrib, ← pow_two]
    exact hμ.square σ hσ
  · have hm : ∃ s, ∀ t, τ t ≠ σ s := by
      have hh := mt (four_coverage τ σ hσ).mp h
      push Not at hh
      exact hh
    obtain ⟨s, hs⟩ := hm
    exact int_missing μ w hμ (by omega) τ σ hσ s hs

private lemma sum_tuples (A : (Fin 4 → Fin n) → ℝ) :
    (∑ τ, A τ) = ∑ i, ∑ j, ∑ k, ∑ l, A ![i, j, k, l] := by
  let e : (Fin 4 → Fin n) ≃ (Fin n × Fin n × Fin n × Fin n) :=
    { toFun := fun τ => (τ 0, τ 1, τ 2, τ 3)
      invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      left_inv := fun τ => by funext i; fin_cases i <;> rfl
      right_inv := fun p => by rcases p with ⟨i, j, k, l⟩; rfl }
  rw [Fintype.sum_equiv e A (fun p => A (e.symm p))
    (by intro τ; simp)]
  simp only [Fintype.sum_prod_type]
  rfl

private lemma sum_four (σ : Fin 4 → Fin n) (hσ : Function.Injective σ)
    (A : (Fin 4 → Fin n) → ℝ) (w : ℝ) :
    (∑ τ, A τ * (if ∃ π : Equiv.Perm (Fin 4), τ = σ ∘ π then w else 0)) =
      w * ∑ π : Equiv.Perm (Fin 4), A (σ ∘ π) := by
  classical
  have hi : Function.Injective (fun π : Equiv.Perm (Fin 4) => σ ∘ π) := by
    intro π ρ h
    apply Equiv.ext
    intro s
    exact hσ (congrFun h s)
  let b : (Fin 4 → Fin n) → ℝ := fun τ =>
    A τ * (if ∃ π : Equiv.Perm (Fin 4), τ = σ ∘ π then w else 0)
  have hs : (∑ τ, b τ) = ∑ τ ∈ Finset.univ.image (fun π : Equiv.Perm (Fin 4) => σ ∘ π), b τ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro τ _ ht
    have hn : ¬ ∃ π : Equiv.Perm (Fin 4), τ = σ ∘ π := by
      intro ⟨π, hπ⟩
      apply ht
      exact Finset.mem_image.mpr ⟨π, Finset.mem_univ _, hπ.symm⟩
    simp [b, hn]
  rw [hs, Finset.sum_image (fun π _ ρ _ h => hi h)]
  simp only [b, show ∀ π : Equiv.Perm (Fin 4),
    (∃ ρ : Equiv.Perm (Fin 4), σ ∘ π = σ ∘ ρ) from fun π => ⟨π, rfl⟩,
    ↓reduceIte]
  rw [← Finset.sum_mul]
  ring

private lemma integ0 (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) :
    Integrable (fun x => ∏ s, x (σ s)) μ := by
  exact hμ.integ 4 (by omega) σ

private lemma integ1 (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (i : Fin n) :
    Integrable (fun x => x i * ∏ s, x (σ s)) μ := by
  simpa [Fin.prod_univ_succ] using integ_prod μ w hμ (by omega) ![i] σ

private lemma integ2 (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (i j : Fin n) :
    Integrable (fun x => (x i * x j) * ∏ s, x (σ s)) μ := by
  simpa [Fin.prod_univ_succ] using integ_prod μ w hμ (by omega) ![i, j] σ

private lemma integ3 (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (i j k : Fin n) :
    Integrable (fun x => (x i * x j * x k) * ∏ s, x (σ s)) μ := by
  simpa [Fin.prod_univ_succ, mul_assoc] using integ_prod μ w hμ (by omega) ![i, j, k] σ

private lemma int0 (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (hσ : Function.Injective σ) :
    (∫ x, ∏ s, x (σ s) ∂μ) = 0 := by
  simpa using int_short μ w hμ (r := 0) (by omega) Fin.elim0 σ hσ

private lemma int1 (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (hσ : Function.Injective σ) (i : Fin n) :
    (∫ x, x i * ∏ s, x (σ s) ∂μ) = 0 := by
  simpa [Fin.prod_univ_succ] using int_short μ w hμ (by omega) ![i] σ hσ

private lemma int2 (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (hσ : Function.Injective σ) (i j : Fin n) :
    (∫ x, (x i * x j) * ∏ s, x (σ s) ∂μ) = 0 := by
  simpa [Fin.prod_univ_succ] using int_short μ w hμ (by omega) ![i, j] σ hσ

private lemma int3 (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (hσ : Function.Injective σ) (i j k : Fin n) :
    (∫ x, (x i * x j * x k) * ∏ s, x (σ s) ∂μ) = 0 := by
  simpa [Fin.prod_univ_succ, mul_assoc] using int_short μ w hμ (by omega) ![i, j, k] σ hσ

private lemma integral_value_sum {ι : Type*} [Fintype ι]
    (μ : Measure (Fin n → ℝ)) (p : ι → (Fin n → ℝ) → ℝ) (b : ι → ℝ)
    (h : ∀ i, Integrable (p i) μ ∧ (∫ x, p i x ∂μ) = b i) :
    Integrable (fun x => ∑ i, p i x) μ ∧ (∫ x, ∑ i, p i x ∂μ) = ∑ i, b i := by
  constructor
  · exact integrable_finsetSum _ (fun i _ => (h i).1)
  · rw [integral_finsetSum _ (fun i _ => (h i).1)]
    simp only [(h _).2]

private lemma integral_value_mul (μ : Measure (Fin n → ℝ))
    (p : (Fin n → ℝ) → ℝ) (b a : ℝ)
    (h : Integrable p μ ∧ (∫ x, p x ∂μ) = b) :
    Integrable (fun x => a * p x) μ ∧ (∫ x, a * p x ∂μ) = a * b := by
  exact ⟨h.1.const_mul a, by rw [integral_const_mul, h.2]⟩

local notation "lin" => (fun (a : Fin n → ℝ) (x : Fin n → ℝ) => ∑ i, a i * x i)
local notation "quad" => (fun (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) =>
  ∑ i, ∑ j, A i j * (x i * x j))

private lemma value_lin (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (hσ : Function.Injective σ)
    (a : Fin n → ℝ) :
    Integrable (fun x => lin a x * ∏ s, x (σ s)) μ ∧
      (∫ x, lin a x * ∏ s, x (σ s) ∂μ) = 0 := by
  have h := integral_value_sum μ
    (fun i x => a i * (x i * ∏ s, x (σ s))) (fun _ => 0)
    (fun i => by simpa using (integral_value_mul μ _ 0 (a i)
      ⟨integ1 μ w hμ σ i, int1 μ w hμ σ hσ i⟩))
  simpa only [Finset.sum_mul, mul_assoc, Finset.sum_const_zero] using h

private lemma value_quad (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (hσ : Function.Injective σ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => quad A x * ∏ s, x (σ s)) μ ∧
      (∫ x, quad A x * ∏ s, x (σ s) ∂μ) = 0 := by
  have h := integral_value_sum μ
    (fun i x => ∑ j, A i j * ((x i * x j) * ∏ s, x (σ s))) (fun _ => 0)
    (fun i => by simpa using (integral_value_sum μ
      (fun j x => A i j * ((x i * x j) * ∏ s, x (σ s))) (fun _ => 0)
      (fun j => by simpa using (integral_value_mul μ _ 0 (A i j)
        ⟨integ2 μ w hμ σ i j, int2 μ w hμ σ hσ i j⟩))))
  simpa only [Finset.sum_mul, mul_assoc, Finset.sum_const_zero] using h

private lemma value_ll (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (hσ : Function.Injective σ)
    (a b : Fin n → ℝ) :
    Integrable (fun x => (lin a x * lin b x) * ∏ s, x (σ s)) μ ∧
      (∫ x, (lin a x * lin b x) * ∏ s, x (σ s) ∂μ) = 0 := by
  have expand (x : Fin n → ℝ) : (lin a x * lin b x) * ∏ s, x (σ s) =
      ∑ i, ∑ j, (a i * b j) * ((x i * x j) * ∏ s, x (σ s)) := by
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [expand]
  have h := integral_value_sum μ
    (fun i x => ∑ j, (a i * b j) * ((x i * x j) * ∏ s, x (σ s))) (fun _ => 0)
    (fun i => by simpa using (integral_value_sum μ
      (fun j x => (a i * b j) * ((x i * x j) * ∏ s, x (σ s))) (fun _ => 0)
      (fun j => by simpa using (integral_value_mul μ _ 0 (a i * b j)
        ⟨integ2 μ w hμ σ i j, int2 μ w hμ σ hσ i j⟩))))
  simpa using h

private lemma value_lq (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (hσ : Function.Injective σ)
    (a : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => (lin a x * quad A x) * ∏ s, x (σ s)) μ ∧
      (∫ x, (lin a x * quad A x) * ∏ s, x (σ s) ∂μ) = 0 := by
  have expand (x : Fin n → ℝ) : (lin a x * quad A x) * ∏ s, x (σ s) =
      ∑ i, ∑ j, ∑ k, (a i * A j k) * ((x i * x j * x k) * ∏ s, x (σ s)) := by
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [expand]
  have h := integral_value_sum μ
    (fun i x => ∑ j, ∑ k, (a i * A j k) * ((x i * x j * x k) * ∏ s, x (σ s)))
    (fun _ => 0) (fun i => by simpa using (integral_value_sum μ
      (fun j x => ∑ k, (a i * A j k) * ((x i * x j * x k) * ∏ s, x (σ s)))
      (fun _ => 0) (fun j => by simpa using (integral_value_sum μ
        (fun k x => (a i * A j k) * ((x i * x j * x k) * ∏ s, x (σ s)))
        (fun _ => 0) (fun k => by simpa using (integral_value_mul μ _ 0 (a i * A j k)
          ⟨integ3 μ w hμ σ i j k, int3 μ w hμ σ hσ i j k⟩))))))
  simpa using h

private lemma value_qq (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (hσ : Function.Injective σ)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => (quad A x * quad B x) * ∏ s, x (σ s)) μ ∧
      (∫ x, (quad A x * quad B x) * ∏ s, x (σ s) ∂μ) =
        w * ∑ π : Equiv.Perm (Fin 4), A (σ (π 0)) (σ (π 1)) * B (σ (π 2)) (σ (π 3)) := by
  classical
  let p : (Fin 4 → Fin n) → (Fin n → ℝ) → ℝ := fun τ x =>
    (A (τ 0) (τ 1) * B (τ 2) (τ 3)) * ((∏ t, x (τ t)) * ∏ s, x (σ s))
  let b : (Fin 4 → Fin n) → ℝ := fun τ =>
    (A (τ 0) (τ 1) * B (τ 2) (τ 3)) *
      (if ∃ π : Equiv.Perm (Fin 4), τ = σ ∘ π then w else 0)
  have hv : ∀ τ, Integrable (p τ) μ ∧ (∫ x, p τ x ∂μ) = b τ := by
    intro τ
    exact integral_value_mul μ _ _ _
      ⟨integ_prod μ w hμ (by omega) τ σ, int_four μ w hμ τ σ hσ⟩
  have hs := integral_value_sum μ p b hv
  have expand (x : Fin n → ℝ) : (quad A x * quad B x) * ∏ s, x (σ s) = ∑ τ, p τ x := by
    dsimp only
    rw [sum_tuples]
    have ht (i j k l : Fin n) :
        (∏ t : Fin 4, x (![i, j, k, l] t)) = x i * x j * x k * x l := by
      rw [Fin.prod_univ_four]
      rfl
    simp only [p, ht]
    change (quad A x * quad B x) * (∏ s, x (σ s)) =
      ∑ i, ∑ j, ∑ k, ∑ l, (A i j * B k l) *
        ((x i * x j * x k * x l) * ∏ s, x (σ s))
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    simp only [Finset.sum_mul]
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
  refine ⟨hs.1, hs.2.trans ?_⟩
  exact sum_four σ hσ (fun τ => A (τ 0) (τ 1) * B (τ 2) (τ 3)) w

private lemma mapM_expand (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (k : Fin n) :
    mapM c L Q x k = c k + lin (L k) x + quad (Q k) x := by
  simp only [mapM, mul_assoc]

private lemma value_map (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (hσ : Function.Injective σ)
    (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Integrable (fun x => mapM c L Q x k * ∏ s, x (σ s)) μ ∧
      (∫ x, mapM c L Q x k * ∏ s, x (σ s) ∂μ) = 0 := by
  have h0 := integ0 μ w hμ σ
  have hl := value_lin μ w hμ σ hσ (L k)
  have hq := value_quad μ w hμ σ hσ (Q k)
  simp_rw [mapM_expand, add_mul]
  constructor
  · exact ((h0.const_mul _).add hl.1).add hq.1
  · rw [integral_add (f := fun x => c k * (∏ s, x (σ s)) + lin (L k) x * (∏ s, x (σ s)))
      (g := fun x => quad (Q k) x * (∏ s, x (σ s)))
      ((h0.const_mul (c k)).add hl.1) hq.1,
      integral_add (f := fun x => c k * (∏ s, x (σ s)))
      (g := fun x => lin (L k) x * (∏ s, x (σ s)))
      (h0.const_mul (c k)) hl.1, integral_const_mul,
      int0 μ w hμ σ hσ, hl.2, hq.2]
    ring

private lemma value_pair (μ : Measure (Fin n → ℝ)) (w : ℝ)
    (hμ : SphereParity n μ w) (σ : Fin 4 → Fin n) (hσ : Function.Injective σ)
    (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (k l : Fin n) :
    Integrable (fun x => (mapM c L Q x k * mapM c L Q x l) * ∏ s, x (σ s)) μ ∧
      (∫ x, (mapM c L Q x k * mapM c L Q x l) * ∏ s, x (σ s) ∂μ) =
        w * ∑ π : Equiv.Perm (Fin 4),
          Q k (σ (π 0)) (σ (π 1)) * Q l (σ (π 2)) (σ (π 3)) := by
  have h0 := integ0 μ w hμ σ
  have hlk := value_lin μ w hμ σ hσ (L k)
  have hll := value_lin μ w hμ σ hσ (L l)
  have hqk := value_quad μ w hμ σ hσ (Q k)
  have hql := value_quad μ w hμ σ hσ (Q l)
  have hll' := value_ll μ w hμ σ hσ (L k) (L l)
  have hlq := value_lq μ w hμ σ hσ (L k) (Q l)
  have hql' := value_lq μ w hμ σ hσ (L l) (Q k)
  have hqq := value_qq μ w hμ σ hσ (Q k) (Q l)
  have ilk := hlk.1
  have ill := hll.1
  have iqk := hqk.1
  have iql := hql.1
  have ill' := hll'.1
  have ilq := hlq.1
  have iql' := hql'.1
  have iqq := hqq.1
  have expand (x : Fin n → ℝ) :
      (mapM c L Q x k * mapM c L Q x l) * ∏ s, x (σ s) =
        (c k * c l) * (∏ s, x (σ s))
        + c k * (lin (L l) x * ∏ s, x (σ s))
        + c k * (quad (Q l) x * ∏ s, x (σ s))
        + c l * (lin (L k) x * ∏ s, x (σ s))
        + (lin (L k) x * lin (L l) x) * (∏ s, x (σ s))
        + (lin (L k) x * quad (Q l) x) * (∏ s, x (σ s))
        + c l * (quad (Q k) x * ∏ s, x (σ s))
        + (lin (L l) x * quad (Q k) x) * (∏ s, x (σ s))
        + (quad (Q k) x * quad (Q l) x) * (∏ s, x (σ s)) := by
    rw [mapM_expand, mapM_expand]
    ring
  simp_rw [expand]
  constructor
  · fun_prop
  · simp (disch := fun_prop) only [integral_add]
    simp only [integral_const_mul, int0 μ w hμ σ hσ,
      hlk.2, hll.2, hqk.2, hql.2, hll'.2, hlq.2, hql'.2, hqq.2,
      mul_zero, add_zero, zero_add]

/-- **Parity identifies the coefficient** of `x_S` in `f(m(x))`. -/
theorem parity_coeff (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] (w : ℝ)
    (hμ : SphereParity n μ w) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (σ : Fin 4 → Fin n) (hσ : Function.Injective σ) :
    ∫ x, funF f0 g F (mapM c L Q x) * ∏ s, x (σ s) ∂μ = w * coeffS F Q σ := by
  have h0 := integ0 μ w hμ σ
  have hm (k : Fin n) := value_map μ w hμ σ hσ c L Q k
  have hp (k l : Fin n) := value_pair μ w hμ σ hσ c L Q k l
  have him (k : Fin n) := (hm k).1
  have hip (k l : Fin n) := (hp k l).1
  have expand (x : Fin n → ℝ) :
      funF f0 g F (mapM c L Q x) * ∏ s, x (σ s) =
        f0 * (∏ s, x (σ s))
        + ∑ k, g k * (mapM c L Q x k * ∏ s, x (σ s))
        + ∑ k, ∑ l, F k l * ((mapM c L Q x k * mapM c L Q x l) * ∏ s, x (σ s)) := by
    simp only [funF, add_mul, Finset.sum_mul, mul_assoc]
  simp_rw [expand]
  simp (disch := fun_prop) only [integral_add, integral_finsetSum]
  simp only [integral_const_mul, int0 μ w hμ σ hσ, (hm _).2, (hp _ _).2,
    mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  simp only [coeffS, ← Finset.mul_sum, mul_left_comm]

end BstLean.Part29
