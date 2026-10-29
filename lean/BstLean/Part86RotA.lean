import BstLean.Part86Defs
import BstLean.Part53Laws
import BstLean.Part56Orth_Projection

/-!
# Part 86, RotA: the completion `E` of the anchor features and its linear algebra

* `rotExists`: an orthonormal family `E` with `RotE v E` exists for every unit `v`.
* `rot_sumsq`, `rot_mapMD`, `rot_KR`, `rot_resid`: the finite linear algebra of `Z ↦ (U, W)`.
-/

namespace BstLean.Part86

open MeasureTheory
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD monoVal)
open BstLean.Part41 (Mono phiM colM)
open BstLean.Part53 (linZ)
open BstLean.Part56 (UnitV phiB kJ KR tauR ancRK betaJ)
open BstLean.Part56.Orth (residualFeature block_norm_pos blocks_orthogonal)
open BstLean.Part78 (zv)

variable {n d : ℕ}

/-! ## Evaluation of the feature polynomials -/

theorem eval_monoP (x : Fin n → ℝ) (p : Mono n d) :
    MvPolynomial.eval x (monoP p) = phiM x p := by
  unfold monoP phiM monoVal
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  simp

theorem eval_psPE (E : JR n d → Mono n d → ℝ) (x : Fin n → ℝ) (q : JR n d) :
    MvPolynomial.eval x (psPE E q) = ∑ p, E q p * phiM x p := by
  unfold psPE
  simp [eval_monoP]

theorem phiB_mul_phiM (j : ℕ) (v x : Fin n → ℝ) (p : Mono n d) :
    phiB d j v p * phiM x p = phiB d j v p * phiB d j x p := by
  unfold phiB
  split_ifs <;> simp

theorem sum_phiB_phiM (j : ℕ) (v x : Fin n → ℝ) :
    ∑ p : Mono n d, phiB d j v p * phiM x p = kJ d j x v := by
  unfold kJ
  apply Finset.sum_congr rfl
  intro p _
  rw [phiB_mul_phiM, mul_comm]

theorem eval_bPE (v x : Fin n → ℝ) (j : Fin (d + 1)) :
    MvPolynomial.eval x (bPE d v j) = kJ d j x v / Real.sqrt (kJ d j v v) := by
  unfold bPE
  simp only [map_sum, map_mul, MvPolynomial.eval_C, eval_monoP]
  rw [← sum_phiB_phiM (d := d) j v x, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem monoP_degree (p : Mono n d) : (monoP p).totalDegree ≤ d := by
  unfold monoP
  refine le_trans (MvPolynomial.totalDegree_multiset_prod _) ?_
  rw [Multiset.map_map]
  have h1 : ∀ s : Multiset (Fin n),
      (s.map (MvPolynomial.totalDegree ∘ (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℝ))).sum
        = Multiset.card s := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [ih, add_comm]
  rw [h1]
  have h3 : Multiset.card (p.2 : Multiset (Fin n)) = (p.1 : ℕ) := p.2.2
  have h2 := p.1.2
  omega

theorem bPE_degree (v : Fin n → ℝ) (j : Fin (d + 1)) : (bPE d v j).totalDegree ≤ d := by
  unfold bPE
  apply MvPolynomial.totalDegree_finsetSum_le
  intro p _
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact monoP_degree p

theorem psPE_degree (E : JR n d → Mono n d → ℝ) (q : JR n d) : (psPE E q).totalDegree ≤ d := by
  unfold psPE
  apply MvPolynomial.totalDegree_finsetSum_le
  intro p _
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact monoP_degree p

/-! ## Existence -/

private lemma inner_eucl {ι : Type} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    inner ℝ x y = ∑ p, x p * y p := by
  simp [PiLp.inner_apply, mul_comm]

theorem rotExists (n d : ℕ) : RotExists n d := by
  classical
  intro v hv
  let V := EuclideanSpace ℝ (Mono n d)
  let f : Fin (d + 1) → V := fun j =>
    WithLp.toLp 2 (fun p => phiB d j v p / Real.sqrt (kJ d j v v))
  have hpos : ∀ j : Fin (d + 1), 0 < kJ d j v v := fun j =>
    block_norm_pos v hv j (by have := j.2; omega)
  have hf : Orthonormal ℝ f := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [inner_eucl]
    simp only [f]
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      have h := hpos i
      have hs : Real.sqrt (kJ d i v v) * Real.sqrt (kJ d i v v) = kJ d i v v :=
        Real.mul_self_sqrt h.le
      have : ∀ p : Mono n d, phiB d i v p / Real.sqrt (kJ d i v v) *
          (phiB d i v p / Real.sqrt (kJ d i v v)) = phiB d i v p * phiB d i v p / kJ d i v v := by
        intro p
        rw [div_mul_div_comm, hs]
      simp_rw [this]
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt h)
    · simp only [if_neg hij]
      have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
      have : ∀ p : Mono n d, phiB d i v p / Real.sqrt (kJ d i v v) *
          (phiB d j v p / Real.sqrt (kJ d j v v)) =
          phiB d i v p * phiB d j v p / (Real.sqrt (kJ d i v v) * Real.sqrt (kJ d j v v)) := by
        intro p
        rw [div_mul_div_comm]
      simp_rw [this]
      rw [← Finset.sum_div, blocks_orthogonal _ _ v hne, zero_div]
  have hcard : d + 1 ≤ Fintype.card (Mono n d) := by
    have h := hf.linearIndependent.fintype_card_le_finrank
    simpa [V] using h
  have hc : Module.finrank ℝ V = Fintype.card (Fin (d + 1) ⊕ JR n d) := by
    simp only [V, finrank_euclideanSpace, Fintype.card_sum, Fintype.card_fin]
    omega
  let w : Fin (d + 1) ⊕ JR n d → V := Sum.elim f (fun _ => 0)
  have hw : Orthonormal ℝ ((Set.range Sum.inl : Set (Fin (d + 1) ⊕ JR n d)).restrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨_, ⟨i, rfl⟩⟩ ⟨_, ⟨j, rfl⟩⟩
    have h := (orthonormal_iff_ite.mp hf) i j
    change inner ℝ (f i) (f j) = _
    rw [h]
    by_cases hij : i = j
    · simp [hij]
    · have : ¬ ((⟨Sum.inl i, ⟨i, rfl⟩⟩ : (Set.range Sum.inl : Set (Fin (d + 1) ⊕ JR n d))) =
          ⟨Sum.inl j, ⟨j, rfl⟩⟩) := by
        intro h'
        exact hij (Sum.inl_injective (Subtype.ext_iff.mp h'))
      rw [if_neg hij, if_neg this]
  obtain ⟨b, hb⟩ := hw.exists_orthonormalBasis_extension_of_card_eq hc
  have hbl : ∀ j : Fin (d + 1), b (Sum.inl j) = f j := fun j =>
    (hb (Sum.inl j) ⟨j, rfl⟩).trans rfl
  have hbo := orthonormal_iff_ite.mp b.orthonormal
  refine ⟨fun q p => b (Sum.inr q) p, ?_, ?_, ?_⟩
  · intro q q'
    have h := hbo (Sum.inr q) (Sum.inr q')
    rw [inner_eucl] at h
    rw [h]
    simp
  · intro q j hj
    have hj' : j < d + 1 := Finset.mem_range.mp hj
    have h := hbo (Sum.inr q) (Sum.inl ⟨j, hj'⟩)
    rw [inner_eucl, hbl] at h
    simp only [f, reduceCtorEq, if_false] at h
    have hk := hpos ⟨j, hj'⟩
    have hs : 0 < Real.sqrt (kJ d j v v) := Real.sqrt_pos.mpr hk
    have : ∑ p, b (Sum.inr q) p * phiB d j v p =
        (∑ p, b (Sum.inr q) p * (phiB d j v p / Real.sqrt (kJ d j v v))) *
          Real.sqrt (kJ d j v v) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      field_simp
    rw [this, h, zero_mul]
  · intro p p'
    have h := b.sum_inner_mul_inner (EuclideanSpace.single p (1 : ℝ))
      (EuclideanSpace.single p' (1 : ℝ))
    have h1 : ∀ i, inner ℝ (EuclideanSpace.single p (1 : ℝ)) (b i) = b i p := by
      intro i; simp [EuclideanSpace.inner_single_left]
    have h2 : ∀ i, inner ℝ (b i) (EuclideanSpace.single p' (1 : ℝ)) = b i p' := by
      intro i; rw [inner_eucl]; simp [EuclideanSpace.single_apply]
    simp only [h1, h2] at h
    rw [Fintype.sum_sum_type] at h
    have h3 : inner ℝ (EuclideanSpace.single p (1 : ℝ)) (EuclideanSpace.single p' (1 : ℝ)) =
        if p = p' then 1 else 0 := by
      simp [EuclideanSpace.inner_single_left, eq_comm]
    rw [h3] at h
    rw [← h, add_comm]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun j => phiB d j v p * phiB d j v p' / kJ d j v v)]
    apply Finset.sum_congr rfl
    intro j _
    rw [hbl]
    simp only [f]
    have hk := hpos j
    have hs : Real.sqrt (kJ d j v v) * Real.sqrt (kJ d j v v) = kJ d j v v :=
      Real.mul_self_sqrt hk.le
    rw [div_mul_div_comm, hs]

/-! ## The completeness identity in bilinear form -/

theorem rot_compl (v : Fin n → ℝ) (E : JR n d → Mono n d → ℝ) (hE : RotE v E)
    (a b : Mono n d → ℝ) :
    ∑ p, a p * b p = ∑ q, (∑ p, E q p * a p) * (∑ p, E q p * b p) +
      ∑ j ∈ Finset.range (d + 1),
        (∑ p, phiB d j v p * a p) * (∑ p, phiB d j v p * b p) / kJ d j v v := by
  classical
  obtain ⟨-, -, h3⟩ := hE
  have hL : ∑ p, a p * b p = ∑ p, ∑ p', a p * b p' * (if p = p' then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro p _
    simp
  rw [hL]
  have hR1 : ∑ q, (∑ p, E q p * a p) * (∑ p, E q p * b p) =
      ∑ p, ∑ p', a p * b p' * ∑ q, E q p * E q p' := by
    simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p' _
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hR2 : ∑ j ∈ Finset.range (d + 1),
        (∑ p, phiB d j v p * a p) * (∑ p, phiB d j v p * b p) / kJ d j v v =
      ∑ p, ∑ p', a p * b p' *
        ∑ j ∈ Finset.range (d + 1), phiB d j v p * phiB d j v p' / kJ d j v v := by
    simp_rw [Finset.sum_mul_sum, Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p' _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hR1, hR2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p' _
  rw [← mul_add, h3]

/-! ## The anchors -/

theorem anc_eq (v : Fin n → ℝ) (Z : CoefIdxD n d → ℝ) (j : ℕ) (i : Fin n) :
    ancRK Z v j i = ∑ p : Mono n d, phiB d j v p * colM Z p i := by
  unfold ancRK linZ
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem Uof_anc (v : Fin n → ℝ) (hv : UnitV v) (Z : CoefIdxD n d → ℝ) (j : ℕ) (hj : j ≤ d)
    (i : Fin n) :
    ancRK Z v j i = Real.sqrt (kJ d j v v) * Uof v Z (⟨j, by omega⟩, i) := by
  have hs : 0 < Real.sqrt (kJ d j v v) := Real.sqrt_pos.mpr (block_norm_pos v hv j hj)
  unfold Uof
  simp only
  field_simp

theorem Uof_smul (v : Fin n → ℝ) (c : ℝ) (Z : CoefIdxD n d → ℝ) :
    Uof v (c • Z) = c • Uof v Z := by
  funext a
  simp only [Uof, Pi.smul_apply, smul_eq_mul, anc_eq, colM]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem Wof_smul (E : JR n d → Mono n d → ℝ) (c : ℝ) (Z : CoefIdxD n d → ℝ) :
    Wof E (c • Z) = c • Wof E Z := by
  funext a
  simp only [Wof, Pi.smul_apply, smul_eq_mul, colM]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-! ## The facts -/

theorem rot_sumsq (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ) (hE : RotE v E) :
    ∀ Z : CoefIdxD n d → ℝ, ∑ α, Z α ^ 2 = ∑ a, Uof v Z a ^ 2 + ∑ a, Wof E Z a ^ 2 := by
  classical
  intro Z
  have h0 : ∑ α, Z α ^ 2 = ∑ i : Fin n, ∑ p : Mono n d, colM Z p i * colM Z p i := by
    rw [Finset.sum_comm]
    rw [Fintype.sum_sigma, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro a _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro i _
    simp [colM, pow_two]
  have hU : ∑ a, Uof v Z a ^ 2 = ∑ i : Fin n, ∑ j : Fin (d + 1), Uof v Z (j, i) ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hW : ∑ a, Wof E Z a ^ 2 = ∑ i : Fin n, ∑ q : JR n d, Wof E Z (q, i) ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [h0, hU, hW, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [rot_compl v E hE (fun p => colM Z p i) (fun p => colM Z p i), add_comm]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun j =>
      (∑ p, phiB d j v p * colM Z p i) * (∑ p, phiB d j v p * colM Z p i) / kJ d j v v)]
    apply Finset.sum_congr rfl
    intro j _
    have hk := block_norm_pos (d := d) v hv (j : ℕ) (by have := j.2; omega)
    simp only [Uof, anc_eq]
    rw [div_pow, Real.sq_sqrt hk.le, pow_two]
  · apply Finset.sum_congr rfl
    intro q _
    simp only [Wof, pow_two]

theorem rot_mapMD (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ) (hE : RotE v E) :
    ∀ (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) (i : Fin n),
      mapMD Z x i = ∑ j : Fin (d + 1), MvPolynomial.eval x (bPE d v j) * Uof v Z (j, i) +
        zv (Wof E Z) (fun q => MvPolynomial.eval x (psPE E q)) i := by
  classical
  intro Z x i
  rw [BstLean.Part53.mapMD_linZ]
  unfold linZ
  rw [rot_compl v E hE (fun p => colM Z p i) (fun p => phiM x p), add_comm]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun j =>
      (∑ p, phiB d j v p * colM Z p i) * (∑ p, phiB d j v p * phiM x p) / kJ d j v v)]
    apply Finset.sum_congr rfl
    intro j _
    have hk := block_norm_pos (d := d) v hv (j : ℕ) (by have := j.2; omega)
    have hs : Real.sqrt (kJ d j v v) * Real.sqrt (kJ d j v v) = kJ d j v v :=
      Real.mul_self_sqrt hk.le
    rw [eval_bPE, sum_phiB_phiM]
    simp only [Uof, anc_eq]
    rw [div_mul_div_comm, hs, mul_comm]
  · unfold zv
    apply Finset.sum_congr rfl
    intro q _
    simp only [Wof, eval_psPE]

private lemma mono_zero (x : Fin n → ℝ) (p : Mono n d) (h : (p.1 : ℕ) = 0) : phiM x p = 1 := by
  obtain ⟨⟨i, hi⟩, β⟩ := p
  simp only at h
  subst h
  have : (β : Multiset (Fin n)) = 0 := Multiset.card_eq_zero.mp β.2
  simp [phiM, monoVal, this]

private lemma kJ_zero (x y v : Fin n → ℝ) : kJ d 0 x y = kJ d 0 v v := by
  unfold kJ
  apply Finset.sum_congr rfl
  intro p _
  unfold phiB
  split_ifs with h
  · rw [mono_zero x p h, mono_zero y p h, mono_zero v p h]
  · rfl

theorem sum_phiM_phiM (x y : Fin n → ℝ) :
    ∑ p : Mono n d, phiM x p * phiM y p = ∑ j ∈ Finset.range (d + 1), kJ d j x y := by
  classical
  unfold kJ
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_eq_single (p.1 : ℕ)]
  · simp [phiB]
  · intro j _ h
    simp [phiB, Ne.symm h]
  · intro h
    exact (h (Finset.mem_range.mpr p.1.2)).elim

theorem rot_KR (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ) (hE : RotE v E) :
    ∀ x y : Fin n → ℝ,
      ∑ q, MvPolynomial.eval x (psPE E q) * MvPolynomial.eval y (psPE E q) = KR d v x y := by
  classical
  intro x y
  have h := rot_compl v E hE (fun p => phiM x p) (fun p => phiM y p)
  simp only [sum_phiB_phiM] at h
  rw [sum_phiM_phiM] at h
  simp only [eval_psPE]
  have h' : ∑ q, (∑ p, E q p * phiM x p) * (∑ p, E q p * phiM y p) =
      ∑ j ∈ Finset.range (d + 1), (kJ d j x y - kJ d j x v * kJ d j y v / kJ d j v v) := by
    rw [Finset.sum_sub_distrib]
    linarith
  rw [h']
  have hi : Finset.range (d + 1) = insert 0 (Finset.Icc 1 d) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : kJ d 0 x y - kJ d 0 x v * kJ d 0 y v / kJ d 0 v v = 0 := by
    rw [kJ_zero x y v, kJ_zero x v v, kJ_zero y v v,
      mul_div_cancel_right₀ _ (ne_of_gt (block_norm_pos v hv 0 (by omega))), sub_self]
  rw [hi, Finset.sum_insert (by simp), h0, zero_add]
  rfl

theorem rot_resid (v : Fin n → ℝ) (E : JR n d → Mono n d → ℝ) (hE : RotE v E) :
    ∀ c : JR n d → ℝ, ∃ c' : Mono n d → ℝ, ∑ p, c' p ^ 2 = ∑ q, c q ^ 2 ∧
      ∀ x : Fin n → ℝ, ∑ q, c q * MvPolynomial.eval x (psPE E q) =
        ∑ p, c' p * residualFeature v x p := by
  classical
  intro c
  obtain ⟨h1, h2, -⟩ := hE
  refine ⟨fun p => ∑ q, c q * E q p, ?_, ?_⟩
  · have : ∀ p : Mono n d, (∑ q, c q * E q p) ^ 2 =
        ∑ q, ∑ q', c q * c q' * (E q p * E q' p) := by
      intro p
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro q' _
      ring
    simp_rw [this]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, h1]
    simp [pow_two]
  · intro x
    have hanc : ∀ j ∈ Finset.range (d + 1),
        ∑ p, (∑ q, c q * E q p) * phiB d j v p = 0 := by
      intro j hj
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro q _
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, h2 q j hj, mul_zero]
    have hres : ∑ p, (∑ q, c q * E q p) * residualFeature v x p =
        ∑ p, (∑ q, c q * E q p) * phiM x p := by
      unfold residualFeature
      simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ j ∈ Finset.range (d + 1),
          ∑ p : Mono n d, (∑ q, c q * E q p) * (betaJ d j v x * phiB d j v p) = 0 := by
        intro j hj
        have h := hanc j hj
        calc ∑ p : Mono n d, (∑ q, c q * E q p) * (betaJ d j v x * phiB d j v p)
            = betaJ d j v x * ∑ p, (∑ q, c q * E q p) * phiB d j v p := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p _
              ring
          _ = 0 := by rw [h, mul_zero]
      rw [Finset.sum_eq_zero this, sub_zero]
    rw [hres]
    simp only [eval_psPE]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring

end BstLean.Part86

#print axioms BstLean.Part86.rotExists
#print axioms BstLean.Part86.rot_sumsq
#print axioms BstLean.Part86.rot_mapMD
#print axioms BstLean.Part86.rot_KR
#print axioms BstLean.Part86.rot_resid
