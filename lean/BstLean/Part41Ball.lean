import BstLean.Part41Hyper

/-!
# Part 41, wave 1: the small ball of the pure part (Lemma `LF-ball`, step (1))

Paper: Lemma `LF-ball`, step (1), of `proofs/option-m/41-arbitrary-degree.tex`. Specification:
`delegations/answers/p41-spec-opus.md`. Do not use `native_decide`. This file imports the statements of
`Part41Hyper` (`bonami_gauss`, `cantelli`), not their proofs.

Route. Each `q_S[b_s]` is a multilinear polynomial of degree `s ≤ k` in the entries of the pure columns
`Z_β`, `β ⊂ S` (distinct columns in a partition), so `bonami_gauss` gives `Var q_S² ≤ (9^k − 1)(E q_S²)²`.
`q_S` and `q_{S'}` are independent when `|S ∩ S'| < d` (no common `d`-subset). `E q_S²` is constant on
each level. Bound each dependent covariance by Cauchy–Schwarz, and the fraction of dependent pairs at
levels `(s, s')` by `q_n` (the hypergeometric overlap tail increases with both set sizes, and `s, s' ≤ k`).
So `Var P_α ≤ (9^k − 1) q_n (E P_α)²`; then `cantelli` at `a = (1 − ϑ) E P_α`.
-/

namespace BstLean.Part41

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)

variable {n d : ℕ}

private lemma polynomial_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) :
    Integrable (fun z => MvPolynomial.eval z p) (stdGauss ι) := by
  classical
  conv in MvPolynomial.eval _ p => rw [p.as_sum]
  simp only [MvPolynomial.eval_sum]
  apply integrable_finsetSum
  intro e he
  simp only [MvPolynomial.eval_monomial]
  have hp (z : ι → ℝ) : e.prod (fun i a => z i ^ a) = ∏ i, z i ^ e i :=
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
  simp_rw [hp]
  exact (Integrable.fintype_prod (f := fun i x => x ^ e i) (fun i =>
    ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet
      (X := fun x : ℝ => x) (μ := ProbabilityTheory.gaussianReal 0 1)
      (by simp) _)).const_mul _

private lemma colP_polynomial (β : Finset (Fin n)) (a : Fin n) :
    ∃ p : MvPolynomial (CoefIdxD n d) ℝ, ∀ Z, colP Z β a = MvPolynomial.eval Z p := by
  classical
  by_cases h : β.card = d
  · refine ⟨MvPolynomial.X ⟨Fin.last d, (⟨β.val, h⟩, a)⟩, ?_⟩
    intro Z
    simp [colP, h]
  · exact ⟨0, fun Z => by simp [colP, h]⟩

private lemma qS_polynomial {s : ℕ} (b : (Fin s → Fin n) → ℝ)
    (S : Finset (Fin n)) :
    ∃ p : MvPolynomial (CoefIdxD n d) ℝ, ∀ Z, qS b S Z = MvPolynomial.eval Z p := by
  classical
  choose p hp using (colP_polynomial (n := n) (d := d))
  refine ⟨MvPolynomial.C ((Real.sqrt (BstLean.Part36.rhoD n (s * d)))⁻¹) *
    ∑ π ∈ parts d s S, ∑ w : Fin s → Fin n,
      MvPolynomial.C (b w) * ∏ t, p (π t) (w t), ?_⟩
  intro Z
  simp [qS, contr, hp]

private lemma Palpha_polynomial (k : ℕ) (T : Tens n) :
    ∃ p : MvPolynomial (CoefIdxD n d) ℝ,
      ∀ Z, Palpha k T Z = MvPolynomial.eval Z p := by
  classical
  choose p hp using (fun s S => qS_polynomial (d := d) (bEff n d k T s) S)
  refine ⟨∑ s ∈ Finset.Icc 1 k,
    MvPolynomial.C (((n : ℝ) ^ (k - s))⁻¹) *
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d), p s S ^ 2, ?_⟩
  intro Z
  simp [Palpha, hp, div_eq_mul_inv, mul_comm]

private lemma Palpha_memLp (k : ℕ) (T : Tens n) :
    MemLp (Palpha (d := d) k T) 2 (stdGauss (CoefIdxD n d)) := by
  classical
  obtain ⟨p, hp⟩ := Palpha_polynomial (d := d) k T
  have he : Palpha (d := d) k T = fun Z => MvPolynomial.eval Z p := funext hp
  have hi : Integrable (Palpha (d := d) k T) (stdGauss (CoefIdxD n d)) := by
    rw [he]
    exact polynomial_integrable p
  apply (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr
  rw [he]
  have hi2 := polynomial_integrable (p ^ 2)
  simp_rw [MvPolynomial.eval_pow] at hi2
  exact hi2

private lemma Palpha_nonneg (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) :
    0 ≤ Palpha k T Z := by
  unfold Palpha
  exact Finset.sum_nonneg fun s hs => div_nonneg
    (Finset.sum_nonneg fun S hS => sq_nonneg _) (by positivity)

private lemma qS_continuous {s : ℕ} (b : (Fin s → Fin n) → ℝ)
    (S : Finset (Fin n)) : Continuous (qS (d := d) b S) := by
  obtain ⟨p, hp⟩ := qS_polynomial (d := d) b S
  rw [show qS (d := d) b S = fun Z => MvPolynomial.eval Z p from funext hp]
  exact p.continuous_eval

private lemma qS_sq_memLp {s : ℕ} (b : (Fin s → Fin n) → ℝ)
    (S : Finset (Fin n)) :
    MemLp (fun Z => qS (d := d) b S Z ^ 2) 2 (stdGauss (CoefIdxD n d)) := by
  obtain ⟨p, hp⟩ := qS_polynomial (d := d) b S
  have hi (r : ℕ) : Integrable (fun Z => qS (d := d) b S Z ^ r)
      (stdGauss (CoefIdxD n d)) := by
    have h := polynomial_integrable (p ^ r)
    simp_rw [MvPolynomial.eval_pow, ← hp] at h
    exact h
  apply (memLp_two_iff_integrable_sq (hi 2).aestronglyMeasurable).mpr
  simpa only [← pow_mul] using hi 4

private lemma finset_perm_of_card_eq (S U : Finset (Fin n)) (hc : S.card = U.card) :
    ∃ e : Equiv.Perm (Fin n), S.map e.toEmbedding = U := by
  classical
  let e0 : (↑S : Set (Fin n)) ≃ (↑U : Set (Fin n)) :=
    Fintype.equivOfCardEq (by simpa using hc)
  let e1 : ((↑S : Set (Fin n))ᶜ : Set (Fin n)) ≃ ((↑U : Set (Fin n))ᶜ : Set (Fin n)) :=
    Fintype.equivOfCardEq (by
      change Fintype.card {x : Fin n // x ∉ S} = Fintype.card {x : Fin n // x ∉ U}
      simp only [Fintype.card_subtype_compl, Fintype.card_coe, hc])
  obtain ⟨e, he⟩ := (Equiv.Set.compl e0).symm e1
  refine ⟨e, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
    have hh := he ⟨y, hy⟩
    have hu := (e0 ⟨y, hy⟩).property
    change e y = (e0 ⟨y, hy⟩).val at hh
    change (e0 ⟨y, hy⟩).val ∈ U at hu
    rw [← hh] at hu
    have hu' : e y ∈ U := hu
    rw [show e y = x from hxy] at hu'
    exact hu'
  · intro hx
    obtain ⟨y, hy⟩ := e0.surjective ⟨x, hx⟩
    exact Finset.mem_map.mpr ⟨y.val, y.property,
      (he y).trans (congrArg Subtype.val hy)⟩

private lemma parts_map {s : ℕ} (e : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (π : Fin s → Finset (Fin n)) (hπ : π ∈ parts d s S) :
    (fun t => (π t).map e.toEmbedding) ∈ parts d s (S.map e.toEmbedding) := by
  classical
  obtain ⟨hc, hd, hu⟩ := (Finset.mem_filter.mp hπ).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, (fun t => by simpa using hc t), ?_, ?_⟩
  · intro t u htu
    exact (Finset.disjoint_map e.toEmbedding).mpr (hd t u htu)
  · simp only [Finset.map_eq_image]
    rw [← Finset.biUnion_image, hu]

private lemma qS_relabel {s : ℕ} (e : Equiv.Perm (Fin n))
    (b : (Fin s → Fin n) → ℝ) (S : Finset (Fin n)) (Z : CoefIdxD n d → ℝ) :
    qS b (S.map e.toEmbedding) Z = qS b S
      (fun α => Z ((Equiv.sigmaCongrRight fun _i : Fin (d + 1) =>
        (Sym.equivCongr e).prodCongr (Equiv.refl (Fin n))) α)) := by
  classical
  unfold qS
  congr 1
  symm
  apply Finset.sum_bij (fun π hπ => fun t => (π t).map e.toEmbedding)
  · exact fun π hπ => parts_map e S π hπ
  · intro π hπ τ hτ he
    funext t
    exact Finset.map_injective e.toEmbedding (congrFun he t)
  · intro τ hτ
    refine ⟨fun t => (τ t).map e.symm.toEmbedding, ?_, ?_⟩
    · have hm := parts_map e.symm (S.map e.toEmbedding) τ hτ
      have hinv : (S.map e.toEmbedding).map e.symm.toEmbedding = S := by
        ext x
        simp
      rw [hinv] at hm
      exact hm
    · funext t
      simp only [Finset.map_map]
      ext x
      simp
  · intro π hπ
    unfold contr
    apply Finset.sum_congr rfl
    intro w hw
    congr 1
    apply Finset.prod_congr rfl
    intro t ht
    have hc := (Finset.mem_filter.mp hπ).2.1 t
    have hcm : ((π t).map e.toEmbedding).card = d := by simpa using hc
    simp only [colP, dite_eq_left hc, dite_eq_left hcm]
    congr 1

private lemma qS_sq_mean_eq {s : ℕ} (b : (Fin s → Fin n) → ℝ)
    (S U : Finset (Fin n)) (hc : S.card = U.card) :
    (∫ Z, qS (d := d) b S Z ^ 2 ∂stdGauss (CoefIdxD n d)) =
      ∫ Z, qS b U Z ^ 2 ∂stdGauss (CoefIdxD n d) := by
  classical
  obtain ⟨e, he⟩ := finset_perm_of_card_eq S U hc
  let ec : Equiv.Perm (CoefIdxD n d) := Equiv.sigmaCongrRight fun i : Fin (d + 1) =>
    (Sym.equivCongr e).prodCongr (Equiv.refl (Fin n))
  let F := MeasurableEquiv.piCongrLeft (fun _ : CoefIdxD n d => ℝ) ec.symm
  have hm : MeasurePreserving F (stdGauss (CoefIdxD n d)) (stdGauss (CoefIdxD n d)) :=
    measurePreserving_piCongrLeft (fun _ : CoefIdxD n d => ProbabilityTheory.gaussianReal 0 1) ec.symm
  have hq (Z : CoefIdxD n d → ℝ) : qS b U Z = qS b S (F Z) := by
    rw [← he, qS_relabel]
    congr 1
    funext α
    change Z (ec α) = F Z α
    simp [F, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [← hm.integral_comp F.measurableEmbedding (fun Z => qS b S Z ^ 2)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun Z => by
    change qS b S (F Z) ^ 2 = qS b U Z ^ 2
    rw [hq]))

private lemma parts_block_subset {s : ℕ} (S : Finset (Fin n))
    (π : Fin s → Finset (Fin n)) (hπ : π ∈ parts d s S) (t : Fin s) :
    π t ⊆ S := by
  classical
  have h := (Finset.mem_filter.mp hπ).2.2.2
  rw [← h]
  exact Finset.subset_biUnion_of_mem π (Finset.mem_univ t)

private lemma qS_depends_on_columns {s : ℕ} (b : (Fin s → Fin n) → ℝ)
    (S : Finset (Fin n)) (Z Z' : CoefIdxD n d → ℝ)
    (he : ∀ β : Finset (Fin n), β ⊆ S → ∀ h : β.card = d, ∀ a : Fin n,
      Z ⟨Fin.last d, (⟨β.val, h⟩, a)⟩ = Z' ⟨Fin.last d, (⟨β.val, h⟩, a)⟩) :
    qS b S Z = qS b S Z' := by
  classical
  unfold qS
  congr 1
  apply Finset.sum_congr rfl
  intro π hπ
  unfold contr
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  apply Finset.prod_congr rfl
  intro t ht
  have hc := (Finset.mem_filter.mp hπ).2.1 t
  simp only [colP, dite_eq_left hc]
  exact he (π t) (parts_block_subset S π hπ t) hc (w t)

private lemma functions_independent_on_disjoint {ι : Type*} [Fintype ι]
    (A B : Finset ι) (f h : (ι → ℝ) → ℝ)
    (hf : Measurable f) (hh : Measurable h) (hd : Disjoint A B)
    (hA : ∀ g g', (∀ i ∈ A, g i = g' i) → f g = f g')
    (hB : ∀ g g', (∀ i ∈ B, g i = g' i) → h g = h g') :
    ProbabilityTheory.IndepFun f h (stdGauss ι) := by
  classical
  let restore (U : Finset ι) (x : U → ℝ) (i : ι) : ℝ :=
    if hi : i ∈ U then x ⟨i, hi⟩ else 0
  have hm (U : Finset ι) : Measurable (restore U) := by
    apply measurable_pi_iff.mpr
    intro i
    dsimp [restore]
    split_ifs <;> fun_prop
  have heA (g : ι → ℝ) : f (restore A (fun x => g x)) = f g := by
    apply hA
    intro i hi
    simp only [restore, dite_eq_left hi]
  have heB (g : ι → ℝ) : h (restore B (fun x => g x)) = h g := by
    apply hB
    intro i hi
    simp only [restore, dite_eq_left hi]
  have hi : ProbabilityTheory.iIndepFun (fun i (g : ι → ℝ) => g i)
      (stdGauss ι) := ProbabilityTheory.iIndepFun_pi (fun _ => aemeasurable_id)
  have hind := (hi.indepFun_finset A B hd (fun i => measurable_pi_apply i)).comp
    (hf.comp (hm A)) (hh.comp (hm B))
  change ProbabilityTheory.IndepFun (fun g => f (restore A (fun x => g x)))
    (fun g => h (restore B (fun x => g x))) (stdGauss ι) at hind
  simpa only [heA, heB] using hind

private lemma qS_independent_low_overlap {s r : ℕ}
    (b : (Fin s → Fin n) → ℝ) (c : (Fin r → Fin n) → ℝ)
    (S U : Finset (Fin n)) (hSU : (S ∩ U).card < d) :
    ProbabilityTheory.IndepFun (qS (d := d) b S) (qS (d := d) c U)
      (stdGauss (CoefIdxD n d)) := by
  classical
  let A (V : Finset (Fin n)) : Finset (CoefIdxD n d) := Finset.univ.filter
    fun α => ∃ (β : Finset (Fin n)) (h : β.card = d) (a : Fin n),
      β ⊆ V ∧ α = ⟨Fin.last d, (⟨β.val, h⟩, a)⟩
  have hd : Disjoint (A S) (A U) := by
    apply Finset.disjoint_left.mpr
    intro α hα hα'
    obtain ⟨β, hβ, a, hβS, ha⟩ := (Finset.mem_filter.mp hα).2
    obtain ⟨β', hβ', a', hβU, ha'⟩ := (Finset.mem_filter.mp hα').2
    have hb : β = β' := by
      have he := congrArg (fun x : CoefIdxD n d => x.2.1.1) (ha.symm.trans ha')
      exact Finset.val_injective he
    subst β'
    have hsub : β ⊆ S ∩ U := Finset.subset_inter hβS hβU
    have hcard := Finset.card_le_card hsub
    omega
  apply functions_independent_on_disjoint (A S) (A U) _ _
    (qS_continuous b S).measurable (qS_continuous c U).measurable hd
  · intro Z Z' he
    apply qS_depends_on_columns
    intro β hβS hc a
    apply he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, β, hc, a, hβS, rfl⟩
  · intro Z Z' he
    apply qS_depends_on_columns
    intro β hβU hc a
    apply he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, β, hc, a, hβU, rfl⟩

private lemma qS_sq_product_low_overlap {s r : ℕ}
    (b : (Fin s → Fin n) → ℝ) (c : (Fin r → Fin n) → ℝ)
    (S U : Finset (Fin n)) (hSU : (S ∩ U).card < d) :
    (∫ Z, qS (d := d) b S Z ^ 2 * qS c U Z ^ 2 ∂stdGauss (CoefIdxD n d)) =
      (∫ Z, qS b S Z ^ 2 ∂stdGauss (CoefIdxD n d)) *
      (∫ Z, qS c U Z ^ 2 ∂stdGauss (CoefIdxD n d)) := by
  have hi := (qS_independent_low_overlap b c S U hSU).comp
    (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)
    (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)
  exact hi.integral_fun_mul_eq_mul_integral
    (qS_sq_memLp b S).aestronglyMeasurable (qS_sq_memLp c U).aestronglyMeasurable

private lemma product_X_bounds {ι : Type*} [Fintype ι] {s : ℕ}
    (a : Fin s → ι) (ha : Function.Injective a) :
    (∀ m ∈ (∏ t, (MvPolynomial.X (a t) : MvPolynomial ι ℝ)).support,
      ∀ i, m i ≤ 1) ∧
    (∏ t, (MvPolynomial.X (a t) : MvPolynomial ι ℝ)).totalDegree ≤ s := by
  classical
  constructor
  · intro m hm i
    apply (MvPolynomial.monomial_le_degreeOf i hm).trans
    apply (MvPolynomial.degreeOf_prod_le i Finset.univ _).trans
    simp only [MvPolynomial.degreeOf_X]
    by_cases h : ∃ t, a t = i
    · obtain ⟨t, ht⟩ := h
      have he (u : Fin s) : i = a u ↔ u = t := by
        rw [← ht]
        constructor
        · intro hu; exact (ha hu).symm
        · rintro rfl; rfl
      simp_rw [he]
      simp
    · have he (u : Fin s) : i ≠ a u := by
        intro he; exact h ⟨u, he.symm⟩
      simp [he]
  · apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
    simp

private lemma qS_bonami_polynomial {s : ℕ} (hd : 1 ≤ d)
    (b : (Fin s → Fin n) → ℝ) (S : Finset (Fin n)) :
    ∃ p : MvPolynomial (CoefIdxD n d) ℝ,
      (∀ Z, qS b S Z = MvPolynomial.eval Z p) ∧
      (∀ m ∈ p.support, ∀ i, m i ≤ 1) ∧ p.totalDegree ≤ s := by
  classical
  let A := (parts d s S).attach
  let idx (π : {π // π ∈ parts d s S}) (w : Fin s → Fin n) (t : Fin s) :
      CoefIdxD n d :=
    ⟨Fin.last d, (⟨(π.val t).val, (Finset.mem_filter.mp π.property).2.1 t⟩, w t)⟩
  have hinj (π : {π // π ∈ parts d s S}) (w : Fin s → Fin n) :
      Function.Injective (idx π w) := by
    intro t u he
    by_contra htu
    have hdis := (Finset.mem_filter.mp π.property).2.2.1 t u htu
    have hβ : π.val t = π.val u :=
      Finset.val_injective (congrArg (fun x : CoefIdxD n d => x.2.1.1) he)
    rw [← hβ] at hdis
    have hz : π.val t = ∅ := by simpa using hdis
    have hc := (Finset.mem_filter.mp π.property).2.1 t
    rw [hz] at hc
    simp only [Finset.card_empty] at hc
    omega
  let term (π : {π // π ∈ parts d s S}) (w : Fin s → Fin n) :
      MvPolynomial (CoefIdxD n d) ℝ :=
    MvPolynomial.C ((Real.sqrt (BstLean.Part36.rhoD n (s * d)))⁻¹ * b w) *
      ∏ t, MvPolynomial.X (idx π w t)
  have hterm π w : (∀ i, (term π w).degreeOf i ≤ 1) ∧ (term π w).totalDegree ≤ s := by
    have hb := product_X_bounds (idx π w) (hinj π w)
    constructor
    · intro i
      apply (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
      exact MvPolynomial.degreeOf_le_iff.mpr (fun m hm => hb.1 m hm i)
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      simpa only [MvPolynomial.totalDegree_C, zero_add] using hb.2
  refine ⟨∑ π ∈ A, ∑ w, term π w, ?_, ?_, ?_⟩
  · intro Z
    simp only [MvPolynomial.eval_sum, term, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_prod, MvPolynomial.eval_X]
    unfold qS contr
    rw [Finset.mul_sum]
    rw [← Finset.sum_attach (parts d s S)]
    apply Finset.sum_congr rfl
    intro π hπ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [colP, dite_eq_left ((Finset.mem_filter.mp π.property).2.1 _)]
    dsimp [idx]
    ring
  · intro m hm i
    apply (MvPolynomial.monomial_le_degreeOf i hm).trans
    apply (MvPolynomial.degreeOf_sum_le i A _).trans
    apply Finset.sup_le
    intro π hπ
    apply (MvPolynomial.degreeOf_sum_le i Finset.univ _).trans
    exact Finset.sup_le fun w hw => (hterm π w).1 i
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro π hπ
    apply MvPolynomial.totalDegree_finsetSum_le
    exact fun w hw => (hterm π w).2

private lemma qS_fourth_le {s : ℕ} (hd : 1 ≤ d) (k : ℕ) (hs : s ≤ k)
    (b : (Fin s → Fin n) → ℝ) (S : Finset (Fin n)) :
    (∫ Z, qS (d := d) b S Z ^ 4 ∂stdGauss (CoefIdxD n d)) ≤
      9 ^ k * (∫ Z, qS b S Z ^ 2 ∂stdGauss (CoefIdxD n d)) ^ 2 := by
  obtain ⟨p, hp, hml, hdeg⟩ := qS_bonami_polynomial hd b S
  have hb := (bonami_gauss k p hml (hdeg.trans hs)).2
  simpa only [← hp] using hb

private lemma covariance_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    ProbabilityTheory.covariance X Y P ^ 2 ≤
      ProbabilityTheory.variance X P * ProbabilityTheory.variance Y P := by
  have hp (t : ℝ) : 0 ≤ ProbabilityTheory.variance X P * (t * t) +
      (2 * ProbabilityTheory.covariance X Y P) * t + ProbabilityTheory.variance Y P := by
    have hv := ProbabilityTheory.variance_nonneg ((fun z => t * X z) + Y) P
    rw [ProbabilityTheory.variance_add (hX.const_mul t) hY,
      ProbabilityTheory.variance_const_mul,
      ProbabilityTheory.covariance_const_mul_left] at hv
    nlinarith only [hv]
  have hd := discrim_le_zero hp
  unfold discrim at hd
  nlinarith only [hd]

private lemma covariance_le_relative {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (C ex ey : ℝ)
    (hC : 0 ≤ C) (hex : 0 ≤ ex) (hey : 0 ≤ ey)
    (hx : ProbabilityTheory.variance X P ≤ C * ex ^ 2)
    (hy : ProbabilityTheory.variance Y P ≤ C * ey ^ 2) :
    ProbabilityTheory.covariance X Y P ≤ C * ex * ey := by
  have hsq := covariance_sq_le P X Y hX hY
  have hprod : ProbabilityTheory.variance X P * ProbabilityTheory.variance Y P ≤
      (C * ex ^ 2) * (C * ey ^ 2) :=
    mul_le_mul hx hy (ProbabilityTheory.variance_nonneg Y P) (by positivity)
  have hn : 0 ≤ C * ex * ey := by positivity
  apply le_of_sq_le_sq _ hn
  calc
    _ ≤ _ := hsq.trans hprod
    _ = (C * ex * ey) ^ 2 := by ring

private lemma qS_sq_variance_le {s : ℕ} (hd : 1 ≤ d) (k : ℕ) (hs : s ≤ k)
    (b : (Fin s → Fin n) → ℝ) (S : Finset (Fin n)) :
    ProbabilityTheory.variance (fun Z => qS (d := d) b S Z ^ 2)
        (stdGauss (CoefIdxD n d)) ≤
      (9 ^ k - 1) * (∫ Z, qS b S Z ^ 2 ∂stdGauss (CoefIdxD n d)) ^ 2 := by
  rw [ProbabilityTheory.variance_eq_sub (qS_sq_memLp b S)]
  have hb := qS_fourth_le hd k hs b S
  change (∫ Z, (qS b S Z ^ 2) ^ 2 ∂stdGauss (CoefIdxD n d)) -
    (∫ Z, qS b S Z ^ 2 ∂stdGauss (CoefIdxD n d)) ^ 2 ≤ _
  simp only [← pow_mul, Nat.reduceMul]
  nlinarith only [hb]

private lemma qS_sq_covariance_le {s r : ℕ} (hd : 1 ≤ d) (k : ℕ)
    (hs : s ≤ k) (hr : r ≤ k) (b : (Fin s → Fin n) → ℝ)
    (c : (Fin r → Fin n) → ℝ) (S U : Finset (Fin n)) :
    ProbabilityTheory.covariance (fun Z => qS (d := d) b S Z ^ 2)
        (fun Z => qS c U Z ^ 2) (stdGauss (CoefIdxD n d)) ≤
      if d ≤ (S ∩ U).card then
        (9 ^ k - 1) * (∫ Z, qS b S Z ^ 2 ∂stdGauss (CoefIdxD n d)) *
          (∫ Z, qS c U Z ^ 2 ∂stdGauss (CoefIdxD n d)) else 0 := by
  split_ifs with hSU
  · exact covariance_le_relative _ _ _ (qS_sq_memLp b S) (qS_sq_memLp c U) _ _ _
      (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
      (integral_nonneg fun Z => sq_nonneg _) (integral_nonneg fun Z => sq_nonneg _)
      (qS_sq_variance_le hd k hs b S) (qS_sq_variance_le hd k hr c U)
  · rw [ProbabilityTheory.covariance_eq_sub (qS_sq_memLp b S) (qS_sq_memLp c U)]
    change (∫ Z, qS b S Z ^ 2 * qS c U Z ^ 2 ∂stdGauss (CoefIdxD n d)) -
      (∫ Z, qS b S Z ^ 2 ∂stdGauss (CoefIdxD n d)) *
        (∫ Z, qS c U Z ^ 2 ∂stdGauss (CoefIdxD n d)) ≤ 0
    rw [qS_sq_product_low_overlap (d := d) b c S U (by omega)]
    simp

private lemma Palpha_variance_expansion (k : ℕ) (T : Tens n) :
    ProbabilityTheory.variance (Palpha (d := d) k T) (stdGauss (CoefIdxD n d)) =
      ∑ s ∈ Finset.Icc 1 k, ∑ r ∈ Finset.Icc 1 k,
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d),
          ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard (r * d),
            ProbabilityTheory.covariance (fun Z => qS (bEff n d k T s) S Z ^ 2)
              (fun Z => qS (bEff n d k T r) U Z ^ 2) (stdGauss (CoefIdxD n d))) /
          (n : ℝ) ^ (k - r) / (n : ℝ) ^ (k - s) := by
  classical
  have hlevel (s : ℕ) : MemLp (fun Z =>
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d),
        qS (bEff n d k T s) S Z ^ 2) 2 (stdGauss (CoefIdxD n d)) :=
    memLp_finsetSum _ (fun S hS => qS_sq_memLp _ S)
  unfold Palpha
  rw [ProbabilityTheory.variance_fun_sum'
    (fun s hs => by
      simpa only [div_eq_mul_inv] using (hlevel s).mul_const (((n : ℝ) ^ (k - s))⁻¹))]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  rw [ProbabilityTheory.covariance_fun_div_left,
    ProbabilityTheory.covariance_fun_div_right,
    ProbabilityTheory.covariance_fun_sum_left' (fun S hS => qS_sq_memLp _ S) (hlevel r)]
  congr 2
  apply Finset.sum_congr rfl
  intro S hS
  rw [ProbabilityTheory.covariance_fun_sum_right'
    (fun U hU => qS_sq_memLp _ U) (qS_sq_memLp _ S)]

private lemma Palpha_variance_le_dependent (hd : 1 ≤ d) (k : ℕ) (T : Tens n) :
    ProbabilityTheory.variance (Palpha (d := d) k T) (stdGauss (CoefIdxD n d)) ≤
      ∑ s ∈ Finset.Icc 1 k, ∑ r ∈ Finset.Icc 1 k,
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d),
          ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard (r * d),
            if d ≤ (S ∩ U).card then
              (9 ^ k - 1) *
                (∫ Z, qS (bEff n d k T s) S Z ^ 2 ∂stdGauss (CoefIdxD n d)) *
                (∫ Z, qS (bEff n d k T r) U Z ^ 2 ∂stdGauss (CoefIdxD n d))
            else 0) / (n : ℝ) ^ (k - r) / (n : ℝ) ^ (k - s) := by
  classical
  rw [Palpha_variance_expansion]
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro r hr
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro S hS
  apply Finset.sum_le_sum
  intro U hU
  exact qS_sq_covariance_le hd k (Finset.mem_Icc.mp hs).2 (Finset.mem_Icc.mp hr).2
    (bEff n d k T s) (bEff n d k T r) S U

private theorem overlap_fixed (n a b j : ℕ) (hj : j ≤ b) (S : Finset (Fin n))
    (hS : S.card = a) :
    ((Finset.univ.powersetCard b).filter
      (fun T : Finset (Fin n) => (S ∩ T).card = j)).card =
      Nat.choose a j * (n - a).choose (b - j) := by
  classical
  have hbij : ((Finset.univ.powersetCard b).filter
      (fun T : Finset (Fin n) => (S ∩ T).card = j)).card =
      (S.powersetCard j ×ˢ (Finset.univ \ S).powersetCard (b - j)).card := by
    apply Finset.card_bij (fun T _ => (S ∩ T, T \ S))
    · intro T hT
      obtain ⟨hT, hST⟩ := Finset.mem_filter.mp hT
      have hTc := (Finset.mem_powersetCard.mp hT).2
      simp only [Finset.mem_product, Finset.mem_powersetCard]
      refine ⟨⟨Finset.inter_subset_left, hST⟩, ⟨?_, ?_⟩⟩
      · intro x hx
        simp only [Finset.mem_sdiff] at hx ⊢
        exact ⟨Finset.mem_univ _, hx.2⟩
      · rw [Finset.card_sdiff, hST, hTc]
    · intro T hT U hU h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      apply Finset.ext
      intro x
      have hi : (x ∈ S ∧ x ∈ T) ↔ (x ∈ S ∧ x ∈ U) := by
        simpa only [Finset.mem_inter] using (congrArg (fun V => x ∈ V) h1).to_iff
      have hd : (x ∈ T ∧ x ∉ S) ↔ (x ∈ U ∧ x ∉ S) := by
        simpa only [Finset.mem_sdiff] using (congrArg (fun V => x ∈ V) h2).to_iff
      tauto
    · rintro ⟨A, B⟩ hAB
      obtain ⟨⟨hAS, hAc⟩, hBU, hBc⟩ :=
        (Finset.mem_product.mp hAB).imp Finset.mem_powersetCard.mp Finset.mem_powersetCard.mp
      have hdis : Disjoint A B := by
        apply Finset.disjoint_left.mpr
        intro x hxA hxB
        exact (Finset.mem_sdiff.mp (hBU hxB)).2 (hAS hxA)
      have hi : S ∩ (A ∪ B) = A := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        have hb : x ∈ B → x ∉ S := fun hx => (Finset.mem_sdiff.mp (hBU hx)).2
        have ha : x ∈ A → x ∈ S := fun hx => hAS hx
        tauto
      have hd : (A ∪ B) \ S = B := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        have hb : x ∈ B → x ∉ S := fun hx => (Finset.mem_sdiff.mp (hBU hx)).2
        have ha : x ∈ A → x ∈ S := fun hx => hAS hx
        tauto
      refine ⟨A ∪ B, ?_, Prod.ext hi hd⟩
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      rw [Finset.card_union_of_disjoint hdis, hAc, hBc, hi, hAc]
      exact ⟨by omega, rfl⟩
  rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
    hS, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  simp [hS]

private lemma relation_card {α β : Type*} (A : Finset α) (B : Finset β)
    (R : α → β → Prop) [DecidableRel R] (u : ℕ)
    (hu : ∀ a ∈ A, (B.filter (R a)).card = u) :
    ((A ×ˢ B).filter (fun p => R p.1 p.2)).card = A.card * u := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  have hf : ∀ a ∈ A, (∑ b ∈ B, if R a b then 1 else 0) = u := by
    intro a ha
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    exact hu a ha
  rw [Finset.sum_congr rfl hf]
  simp

private lemma regular_relation_comparison {α β : Type*} (A : Finset α) (B : Finset β)
    (R : α → β → Prop) (P : α → Prop) (Q : β → Prop)
    [DecidableRel R] [DecidablePred P] [DecidablePred Q]
    (u v : ℕ) (hu : 0 < u)
    (hrow : ∀ a ∈ A, (B.filter (R a)).card = u)
    (hcol : ∀ b ∈ B, (A.filter (fun a => R a b)).card = v)
    (hup : ∀ a ∈ A, ∀ b ∈ B, R a b → P a → Q b) :
    (A.filter P).card * B.card ≤ (B.filter Q).card * A.card := by
  classical
  have htranspose (C : Finset α) (D : Finset β) :
      ((C ×ˢ D).filter (fun p => R p.1 p.2)).card =
      ((D ×ˢ C).filter (fun p => R p.2 p.1)).card := by
    apply Finset.card_bij (fun p hp => (p.2, p.1))
    · intro p hp
      simpa only [Finset.mem_filter, Finset.mem_product, and_comm, and_left_comm,
        and_assoc] using hp
    · intro p hp q hq he
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
    · intro p hp
      refine ⟨(p.2, p.1), ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_product, and_comm, and_left_comm,
        and_assoc] using hp
  have ht : A.card * u = B.card * v := by
    rw [← relation_card A B R u hrow, htranspose,
      relation_card B A (fun b a => R a b) v hcol]
  have hedge : (A.filter P).card * u ≤ (B.filter Q).card * v := by
    rw [← relation_card (A.filter P) B R u
      (fun a ha => hrow a (Finset.mem_filter.mp ha).1)]
    rw [← relation_card (B.filter Q) A (fun b a => R a b) v
      (fun b hb => hcol b (Finset.mem_filter.mp hb).1), ← htranspose]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hp, hr⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    obtain ⟨ha, hpa⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨ha, Finset.mem_filter.mpr ⟨hb, hup p.1 ha p.2 hb hr hpa⟩⟩, hr⟩
  apply Nat.le_of_mul_le_mul_right ?_ hu
  calc
    (A.filter P).card * B.card * u = B.card * ((A.filter P).card * u) := by ring
    _ ≤ B.card * ((B.filter Q).card * v) := Nat.mul_le_mul_left B.card hedge
    _ = (B.filter Q).card * (B.card * v) := by ring
    _ = (B.filter Q).card * (A.card * u) := by rw [ht]
    _ = (B.filter Q).card * A.card * u := by ring

private lemma qN_nonneg (n d k : ℕ) : 0 ≤ qN n d k := by
  unfold qN
  exact Finset.sum_nonneg fun i hi => by positivity

private lemma overlap_tail_fixed (a b d : ℕ) (S : Finset (Fin n))
    (hS : S.card = a) :
    (((Finset.univ : Finset (Fin n)).powersetCard b).filter
      (fun U => d ≤ (S ∩ U).card)).card =
      ∑ j ∈ Finset.Icc d b, a.choose j * (n - a).choose (b - j) := by
  classical
  let A := ((Finset.univ : Finset (Fin n)).powersetCard b).filter
    fun U => d ≤ (S ∩ U).card
  have hf : ∀ U ∈ A, (S ∩ U).card ∈ Finset.Icc d b := by
    intro U hU
    obtain ⟨hU, hdU⟩ := Finset.mem_filter.mp hU
    have hUb := (Finset.mem_powersetCard.mp hU).2
    exact Finset.mem_Icc.mpr ⟨hdU, hUb ▸ Finset.card_le_card Finset.inter_subset_right⟩
  rw [show (((Finset.univ : Finset (Fin n)).powersetCard b).filter
    (fun U => d ≤ (S ∩ U).card)).card = A.card from rfl,
    Finset.card_eq_sum_card_fiberwise hf]
  apply Finset.sum_congr rfl
  intro j hj
  have he : A.filter (fun U => (S ∩ U).card = j) =
      ((Finset.univ : Finset (Fin n)).powersetCard b).filter
        (fun U => (S ∩ U).card = j) := by
    ext U
    simp only [A, Finset.mem_filter]
    have hdj := (Finset.mem_Icc.mp hj).1
    constructor
    · rintro ⟨⟨hU, hdU⟩, he⟩
      exact ⟨hU, he⟩
    · rintro ⟨hU, he⟩
      exact ⟨⟨hU, by omega⟩, he⟩
  rw [he]
  exact overlap_fixed n a b j (Finset.mem_Icc.mp hj).2 S hS

private lemma qN_eq_overlap_fraction (d k : ℕ) (S : Finset (Fin n))
    (hS : S.card = k * d) :
    qN n d k =
      ((((Finset.univ : Finset (Fin n)).powersetCard (k * d)).filter
        (fun U => d ≤ (S ∩ U).card)).card : ℝ) / (n.choose (k * d) : ℝ) := by
  rw [overlap_tail_fixed (k * d) (k * d) d S hS]
  simp only [qN, Nat.cast_sum, Nat.cast_mul, Finset.sum_div]

private lemma overlap_slice_monotone (b K d : ℕ) (hb : b ≤ K) (hK : K ≤ n)
    (S : Finset (Fin n)) :
    (((Finset.univ : Finset (Fin n)).powersetCard b).filter
      (fun U => d ≤ (S ∩ U).card)).card * n.choose K ≤
    (((Finset.univ : Finset (Fin n)).powersetCard K).filter
      (fun U => d ≤ (S ∩ U).card)).card * n.choose b := by
  classical
  let A := (Finset.univ : Finset (Fin n)).powersetCard b
  let B := (Finset.univ : Finset (Fin n)).powersetCard K
  have hrow : ∀ U ∈ A, (B.filter (fun V => U ⊆ V)).card = (n - b).choose (K - b) := by
    intro U hU
    have hc := (Finset.mem_powersetCard.mp hU).2
    dsimp [B]
    rw [Finset.card_filter_powersetCard_subset U Finset.univ K
      (Finset.subset_univ _) (by omega)]
    simp [hc]
  have hcol : ∀ V ∈ B, (A.filter (fun U => U ⊆ V)).card = K.choose b := by
    intro V hV
    have hc := (Finset.mem_powersetCard.mp hV).2
    have he : A.filter (fun U => U ⊆ V) = V.powersetCard b := by
      ext U
      simp only [A, Finset.mem_filter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      tauto
    rw [he, Finset.card_powersetCard, hc]
  have hcomp := regular_relation_comparison A B (fun U V => U ⊆ V)
    (fun U => d ≤ (S ∩ U).card) (fun V => d ≤ (S ∩ V).card)
    ((n - b).choose (K - b)) (K.choose b) (Nat.choose_pos (by omega)) hrow hcol
    (fun U hU V hV hUV hdU => hdU.trans
      (Finset.card_le_card (Finset.inter_subset_inter_left hUV)))
  simpa only [A, B, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using hcomp

private lemma overlap_fraction_le_qN (d k b : ℕ) (hb : b ≤ k * d) (hkd : k * d ≤ n)
    (S : Finset (Fin n)) (hS : S.card ≤ k * d) :
    ((((Finset.univ : Finset (Fin n)).powersetCard b).filter
      (fun U => d ≤ (S ∩ U).card)).card : ℝ) / (n.choose b : ℝ) ≤ qN n d k := by
  classical
  obtain ⟨V, hSV, hVU, hV⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ S) hS (show k * d ≤ (Finset.univ : Finset (Fin n)).card by simpa)
  have hmono := overlap_slice_monotone b (k * d) d hb hkd S
  have hf : (((Finset.univ : Finset (Fin n)).powersetCard (k * d)).filter
      (fun U => d ≤ (S ∩ U).card)).card ≤
      (((Finset.univ : Finset (Fin n)).powersetCard (k * d)).filter
        (fun U => d ≤ (V ∩ U).card)).card := by
    apply Finset.card_le_card
    intro U hU
    obtain ⟨hU, hSU⟩ := Finset.mem_filter.mp hU
    exact Finset.mem_filter.mpr ⟨hU, hSU.trans
      (Finset.card_le_card (Finset.inter_subset_inter_right hSV))⟩
  have hcross := hmono.trans (Nat.mul_le_mul_right (n.choose b) hf)
  rw [qN_eq_overlap_fraction d k V hV]
  apply (div_le_div_iff₀ (show (0 : ℝ) < n.choose b by exact_mod_cast Nat.choose_pos (hb.trans hkd))
    (show (0 : ℝ) < n.choose (k * d) by exact_mod_cast Nat.choose_pos hkd)).mpr
  exact_mod_cast hcross

private lemma piN_nonneg (n d k : ℕ) (th : ℝ) :
    0 ≤ piN n d k th := by
  have hpow : (1 : ℝ) ≤ 9 ^ k := one_le_pow₀ (by norm_num)
  have hq := qN_nonneg n d k
  unfold piN
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hpow) hq)
    (add_nonneg (mul_nonneg (sub_nonneg.mpr hpow) hq) (sq_nonneg _))

private lemma Palpha_variance_bound (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ)
    (hkd : k * d ≤ n) (T : Tens n) :
    ProbabilityTheory.variance (Palpha (d := d) k T) (stdGauss (CoefIdxD n d)) ≤
      (9 ^ k - 1) * qN n d k *
        (∫ Z, Palpha k T Z ∂stdGauss (CoefIdxD n d)) ^ 2 := by
  classical
  let A (s : ℕ) := (Finset.univ : Finset (Fin n)).powersetCard (s * d)
  let μ (s : ℕ) : ℝ := if h : (A s).Nonempty then
    ∫ Z, qS (bEff n d k T s) h.choose Z ^ 2 ∂stdGauss (CoefIdxD n d) else 0
  let C : ℝ := 9 ^ k - 1
  have hC : 0 ≤ C := sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  have hμ (s : ℕ) : 0 ≤ μ s := by
    dsimp [μ]
    split_ifs
    · exact integral_nonneg fun Z => sq_nonneg _
    · exact le_rfl
  have hsize (s : ℕ) (hs : s ∈ Finset.Icc 1 k) : s * d ≤ n :=
    (Nat.mul_le_mul_right d (Finset.mem_Icc.mp hs).2).trans hkd
  have hmean (s : ℕ) (hs : s ∈ Finset.Icc 1 k) (S : Finset (Fin n)) (hS : S ∈ A s) :
      (∫ Z, qS (bEff n d k T s) S Z ^ 2 ∂stdGauss (CoefIdxD n d)) = μ s := by
    have hA : (A s).Nonempty := by
      apply Finset.powersetCard_nonempty.mpr
      simpa using hsize s hs
    dsimp only [μ]
    rw [dite_eq_left hA]
    apply qS_sq_mean_eq
    exact (Finset.mem_powersetCard.mp hS).2.trans
      (Finset.mem_powersetCard.mp hA.choose_spec).2.symm
  have hi (s : ℕ) : Integrable (fun Z => ∑ S ∈ A s, qS (bEff n d k T s) S Z ^ 2)
      (stdGauss (CoefIdxD n d)) :=
    integrable_finsetSum _ fun S hS => (qS_sq_memLp _ S).integrable one_le_two
  have hE : (∫ Z, Palpha k T Z ∂stdGauss (CoefIdxD n d)) =
      ∑ s ∈ Finset.Icc 1 k, ((A s).card : ℝ) * μ s / (n : ℝ) ^ (k - s) := by
    unfold Palpha
    rw [integral_finsetSum _ (fun s hs => by
      simpa only [div_eq_mul_inv] using (hi s).mul_const (((n : ℝ) ^ (k - s))⁻¹))]
    apply Finset.sum_congr rfl
    intro s hs
    rw [integral_div, integral_finsetSum _ (fun S hS => (qS_sq_memLp _ S).integrable one_le_two)]
    rw [Finset.sum_congr rfl (fun S hS => hmean s hs S hS)]
    simp
  rw [hE]
  apply (Palpha_variance_le_dependent hd k T).trans
  have hpair (s r : ℕ) (hs : s ∈ Finset.Icc 1 k) (hr : r ∈ Finset.Icc 1 k) :
      (∑ S ∈ A s, ∑ U ∈ A r,
        if d ≤ (S ∩ U).card then
          C * (∫ Z, qS (bEff n d k T s) S Z ^ 2 ∂stdGauss (CoefIdxD n d)) *
            (∫ Z, qS (bEff n d k T r) U Z ^ 2 ∂stdGauss (CoefIdxD n d)) else 0) ≤
      ((A s).card : ℝ) * (qN n d k * ((A r).card : ℝ)) * (C * μ s * μ r) := by
    calc
      _ ≤ ∑ S ∈ A s, (qN n d k * ((A r).card : ℝ)) * (C * μ s * μ r) := by
        apply Finset.sum_le_sum
        intro S hS
        have hc : (0 : ℝ) < n.choose (r * d) := by
          exact_mod_cast Nat.choose_pos (hsize r hr)
        have hcount := (div_le_iff₀ hc).mp (overlap_fraction_le_qN d k (r * d)
          (Nat.mul_le_mul_right d (Finset.mem_Icc.mp hr).2) hkd S
          ((Finset.mem_powersetCard.mp hS).2.le.trans
            (Nat.mul_le_mul_right d (Finset.mem_Icc.mp hs).2)))
        have hcA : ((A r).card : ℝ) = (n.choose (r * d) : ℝ) := by simp [A]
        calc
          _ = ((A r).filter (fun U => d ≤ (S ∩ U).card)).card * (C * μ s * μ r) := by
            rw [Finset.sum_congr rfl (fun U hU => by
              rw [hmean s hs S hS, hmean r hr U hU])]
            rw [← Finset.sum_filter]
            simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [hcA] using hcount)
            (mul_nonneg (mul_nonneg hC (hμ s)) (hμ r))
      _ = _ := by simp; ring
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 k, ∑ r ∈ Finset.Icc 1 k,
        ((A s).card : ℝ) * (qN n d k * ((A r).card : ℝ)) * (C * μ s * μ r) /
          (n : ℝ) ^ (k - r) / (n : ℝ) ^ (k - s) := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro r hr
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact hpair s r hs hr
    _ = C * qN n d k *
        (∑ s ∈ Finset.Icc 1 k, ((A s).card : ℝ) * μ s / (n : ℝ) ^ (k - s)) ^ 2 := by
      rw [pow_two]
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- The final probabilistic step, isolated from the overlap estimate. -/
private lemma small_ball_of_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : MemLp X 2 P) (hpos : ∀ z, 0 ≤ X z)
    (c th : ℝ) (hc : 0 ≤ c) (hth : th < 1)
    (hvar : ProbabilityTheory.variance X P ≤ c * (∫ z, X z ∂P) ^ 2) :
    P {z | X z < th * ∫ y, X y ∂P} ≤
      ENNReal.ofReal (c / (c + (1 - th) ^ 2)) := by
  let E := ∫ z, X z ∂P
  have hE : 0 ≤ E := integral_nonneg hpos
  have ht : 0 < 1 - th := sub_pos.mpr hth
  have hden : 0 < c + (1 - th) ^ 2 := by positivity
  by_cases he : E = 0
  · have hempty : {z | X z < th * ∫ y, X y ∂P} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      change ¬ X z < th * E
      rw [he, mul_zero]
      exact not_lt.mpr (hpos z)
    rw [hempty, measure_empty]
    exact bot_le
  have hep : 0 < E := lt_of_le_of_ne hE (Ne.symm he)
  have ha : 0 < (1 - th) * E := mul_pos ht hep
  have hs : {z | X z < th * ∫ y, X y ∂P} ⊆
      {z | X z ≤ (∫ y, X y ∂P) - (1 - th) * E} := by
    intro z hz
    change X z < th * E at hz
    change X z ≤ E - (1 - th) * E
    nlinarith
  apply (measure_mono hs).trans
  apply (cantelli P X hX ((1 - th) * E) ha).trans
  apply ENNReal.ofReal_le_ofReal
  have hv := ProbabilityTheory.variance_nonneg X P
  have hve : ProbabilityTheory.variance X P ≤ c * E ^ 2 := hvar
  have hdv : 0 < ProbabilityTheory.variance X P + ((1 - th) * E) ^ 2 := by
    positivity
  apply (div_le_div_iff₀ hdv hden).mpr
  have hh := mul_le_mul_of_nonneg_right hve (sq_nonneg (1 - th))
  nlinarith only [hh]

/-- **Small ball of `P_α`**: `Pr{P_α < ϑ E P_α} ≤ π_n(ϑ)`. -/
theorem pball (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hkd : k * d ≤ n) (T : Tens n)
    (hT : TSymm k T) (th : ℝ) (h0 : 0 < th) (h1 : th < 1) :
    stdGauss (CoefIdxD n d) {Z | Palpha k T Z < th * ∫ Y, Palpha k T Y ∂stdGauss (CoefIdxD n d)} ≤
      ENNReal.ofReal (piN n d k th) := by
  clear hk hT h0
  have hvar : ProbabilityTheory.variance (Palpha (d := d) k T)
      (stdGauss (CoefIdxD n d)) ≤
      (9 ^ k - 1) * qN n d k *
        (∫ Y, Palpha k T Y ∂stdGauss (CoefIdxD n d)) ^ 2 := by
    exact Palpha_variance_bound hn hd k hkd T
  have hc : 0 ≤ (9 ^ k - 1 : ℝ) * qN n d k :=
    mul_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num))) (qN_nonneg n d k)
  simpa only [piN] using small_ball_of_variance (stdGauss (CoefIdxD n d))
    (Palpha k T) (Palpha_memLp k T) (Palpha_nonneg k T)
    ((9 ^ k - 1) * qN n d k) th hc h1 hvar

end BstLean.Part41
