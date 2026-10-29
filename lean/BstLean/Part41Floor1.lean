import BstLean.Part41Defs
import BstLean.Part33Moments
import BstLean.Part36Index
import BstLean.Part29Bessel
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Part 41, wave 1: the multi-level floor — Bessel step, level means, cascade (Lemmas `LC-mean`, `LF` (i), (ii))

Paper: Lemmas `LC`, `LC-mean` and `LF` (i), (ii) of `proofs/option-m/41-arbitrary-degree.tex`.
Specification: `delegations/answers/p41-spec-opus.md`. Do not use `native_decide`.

Routes.
* `LF_i`: the functions `x^S √ρ_{|S|}(n)`, `S` nonempty squarefree, are orthonormal in
  `L²(uniformSphere)` and orthogonal to constants (sign flips); Bessel gives
  `Var_x 𝒫 ≥ Σ_s Σ_{|S| = sd} w_S² ≥ Σ_s n^{−(k−s)} Σ_S w_S²` (`d ≥ 1` makes the sizes `sd` distinct);
  then Minkowski in the weighted `ℓ²` with `w_S = q_S + (w_S − q_S)`.
* `LC_mean`: different unordered partitions have a block that is not shared, whose column enters
  linearly (mean `0`); for one partition `E b[Z_{β₁}, …]² = ‖b‖²` (distinct pure columns, independent
  `N(0,1)` entries); `b` symmetric makes the `s!` orders equal; then count.
* `nu_bounds`: `‖φ‖² ∈ [2, d+1]` on the sphere and `E x^{2S} = 1/ρ_{|S|}(n)`.
* `cascade`: the paper's step (ii), pure algebra: `a_{s,0} = b_s − Σ_{l≥1} ν_{s,l} a_{s+2l,l}`,
  `(u+v)² ≤ (1+η)u² + (1+1/η)v²`, Cauchy–Schwarz over the `L_s` terms, `frob_trL_le`.
* `EP_lower`: `LC_mean` level by level, and `λ_{n,s}/(s (d!)^s) ≥ λ_{n,k}/(k (d!)^k)` for `s ≤ k ≤ n/d`.
-/

namespace BstLean.Part41

open MeasureTheory
open ProbabilityTheory
open scoped Classical
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD rhoD)

variable {n d : ℕ}

private def GaussianPoly {ι : Type*} (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ p : MvPolynomial ι ℝ, ∀ z, f z = MvPolynomial.eval z p

private lemma gpoly_const {ι : Type*} (c : ℝ) :
    GaussianPoly (fun _ : ι → ℝ => c) := ⟨MvPolynomial.C c, by simp⟩

private lemma gpoly_coord {ι : Type*} (i : ι) :
    GaussianPoly (fun z : ι → ℝ => z i) := ⟨MvPolynomial.X i, by simp⟩

private lemma gpoly_mul {ι : Type*} {f g : (ι → ℝ) → ℝ}
    (hf : GaussianPoly f) (hg : GaussianPoly g) : GaussianPoly (fun z => f z * g z) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, by simp [hp, hq]⟩

private lemma gpoly_pow {ι : Type*} {f : (ι → ℝ) → ℝ}
    (hf : GaussianPoly f) (k : ℕ) : GaussianPoly (fun z => f z ^ k) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p ^ k, by simp [hp]⟩

private lemma gpoly_sum {ι κ : Type*} (s : Finset κ) (f : (ι → ℝ) → κ → ℝ)
    (hf : ∀ i ∈ s, GaussianPoly (fun z => f z i)) : GaussianPoly (fun z => ∑ i ∈ s, f z i) := by
  classical
  choose p hp using fun i : s => hf i i.property
  refine ⟨∑ i : s, p i, ?_⟩
  intro z
  simp only [MvPolynomial.eval_sum, ← hp]
  exact (Finset.sum_coe_sort s (fun i => f z i)).symm

private lemma gpoly_prod {ι κ : Type*} (s : Finset κ) (f : (ι → ℝ) → κ → ℝ)
    (hf : ∀ i ∈ s, GaussianPoly (fun z => f z i)) : GaussianPoly (fun z => ∏ i ∈ s, f z i) := by
  classical
  choose p hp using fun i : s => hf i i.property
  refine ⟨∏ i : s, p i, ?_⟩
  intro z
  simp only [MvPolynomial.eval_prod, ← hp]
  exact (Finset.prod_coe_sort s (fun i => f z i)).symm

private lemma gpoly_integrable {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : GaussianPoly f) : Integrable f (stdGauss ι) := by
  classical
  obtain ⟨p, hp⟩ := hf
  rw [show f = (fun z => MvPolynomial.eval z p) from funext hp]
  conv in MvPolynomial.eval _ p => rw [p.as_sum]
  simp only [MvPolynomial.eval_sum]
  apply integrable_finsetSum
  intro a ha
  simp only [MvPolynomial.eval_monomial]
  have he (z : ι → ℝ) : a.prod (fun i e => z i ^ e) = ∏ i, z i ^ a i :=
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
  simp_rw [he]
  exact (Integrable.fintype_prod (f := fun i x => x ^ a i) (fun i =>
    integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x)
      (μ := gaussianReal 0 1) (by simp) _)).const_mul _

private lemma qS_gpoly {s : ℕ} (b : (Fin s → Fin n) → ℝ) (S : Finset (Fin n)) :
    GaussianPoly (qS b S : (CoefIdxD n d → ℝ) → ℝ) := by
  classical
  unfold qS contr
  apply gpoly_mul (gpoly_const _)
  apply gpoly_sum
  intro π hπ
  apply gpoly_sum
  intro w hw
  apply gpoly_mul (gpoly_const _)
  apply gpoly_prod
  intro t ht
  unfold colP
  dsimp only
  split_ifs
  · exact gpoly_coord _
  · exact gpoly_const 0

private lemma qSquares_integrable {s : ℕ} (b : (Fin s → Fin n) → ℝ) :
    Integrable (fun Z => ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d), qS b S Z ^ 2)
      (stdGauss (CoefIdxD n d)) := by
  apply integrable_finsetSum
  intro S hS
  exact gpoly_integrable (gpoly_pow (qS_gpoly b S) 2)

private lemma enum_exists {ι : Type*} {i : ℕ} (β : Sym ι i) :
    ∃ w : Fin i → ι, Finset.univ.val.map w = β.val := by
  have enum (b : Multiset ι) : ∃ (r : ℕ) (w : Fin r → ι),
      r = b.card ∧ Finset.univ.val.map w = b := by
    induction b using Quot.inductionOn with
    | h a => exact ⟨a.length, a.get, rfl, by simp [Fin.univ_val_map]⟩
  obtain ⟨r, w, hr, hw⟩ := enum β.val
  have hri : r = i := hr.trans β.property
  clear hr
  subst r
  exact ⟨w, hw⟩

private noncomputable def enumSym {ι : Type*} {i : ℕ} (β : Sym ι i) : Fin i → ι :=
  Classical.choose (enum_exists β)

private lemma enumSym_spec {ι : Type*} {i : ℕ} (β : Sym ι i) :
    Finset.univ.val.map (enumSym β) = β.val := Classical.choose_spec (enum_exists β)

private lemma enumSym_injective {ι : Type*} {i : ℕ} :
    Function.Injective (enumSym : Sym ι i → Fin i → ι) := by
  intro β γ h
  apply Subtype.ext
  rw [← enumSym_spec β, ← enumSym_spec γ, h]

private lemma mono_enum {i : ℕ} (β : Sym (Fin n) i) (x : Fin n → ℝ) :
    BstLean.Part36.monoVal x β.val = ∏ t, x (enumSym β t) := by
  rw [BstLean.Part36.monoVal, ← enumSym_spec β, Multiset.map_map]
  rfl

private lemma phiSq_le (x : Fin n → ℝ) (hx : ∑ a, x a ^ 2 = 1) :
    phiSq d x ≤ (d : ℝ) + 1 := by
  classical
  have hlevel (i : ℕ) : (∑ β : Sym (Fin n) i, BstLean.Part36.monoVal x β.val ^ 2) ≤ 1 := by
    calc
      _ = ∑ β : Sym (Fin n) i, ∏ t, x (enumSym β t) ^ 2 := by
        apply Finset.sum_congr rfl
        intro β hβ
        rw [mono_enum, Finset.prod_pow]
      _ ≤ ∑ w : Fin i → Fin n, ∏ t, x (w t) ^ 2 := by
        calc
          _ = ∑ w ∈ Finset.univ.image (enumSym : Sym (Fin n) i → Fin i → Fin n),
              ∏ t, x (w t) ^ 2 := by
            rw [Finset.sum_image (fun β _ γ _ h => enumSym_injective h)]
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun w _ _ => Finset.prod_nonneg (fun t _ => sq_nonneg _))
      _ = ∏ t : Fin i, ∑ a : Fin n, x a ^ 2 :=
        (Fintype.prod_sum (fun (_ : Fin i) (a : Fin n) => x a ^ 2)).symm
      _ = 1 := by simp [hx]
  unfold phiSq phiM
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ i : Fin (d + 1), (1 : ℝ) := Finset.sum_le_sum (fun i _ => hlevel i.val)
    _ = (d : ℝ) + 1 := by simp

private lemma sphere_integrable_local (hn : 1 ≤ n)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable f (uniformSphere n) := by
  let := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma phiSq_cont : Continuous (phiSq d : (Fin n → ℝ) → ℝ) := by
  classical
  unfold phiSq phiM
  apply continuous_finsetSum
  intro p hp
  simp_rw [mono_enum p.2]
  fun_prop

private lemma squarefree_moment (hn : 1 ≤ n) (S : Finset (Fin n)) :
    Integrable (fun x => ∏ a ∈ S, x a ^ 2) (uniformSphere n) ∧
    (∫ x, ∏ a ∈ S, x a ^ 2 ∂uniformSphere n) = 1 / rhoD n S.card := by
  classical
  have hm (x : Fin n → ℝ) : BstLean.Part36.monoVal x (S.val + S.val) =
      ∏ a ∈ S, x a ^ 2 := by
    simp only [BstLean.Part36.monoVal, Multiset.map_add, Multiset.prod_add]
    rw [← pow_two, Finset.prod_pow]
    rfl
  have hg : BstLean.Part36.gpm (S.val + S.val) = 1 := by
    unfold BstLean.Part36.gpm
    apply Finset.prod_eq_one
    intro a ha
    by_cases h : a ∈ S
    · have hc : S.val.count a = 1 := Multiset.count_eq_one_of_mem S.nodup h
      norm_num [Multiset.count_add, hc, BstLean.Part29.gaussMom]
    · have hc : S.val.count a = 0 := Multiset.count_eq_zero.mpr h
      norm_num [Multiset.count_add, hc, BstLean.Part29.gaussMom]
  have h := BstLean.Part36.sphere_multiset (uniformSphere n)
    (BstLean.Part33.uniformSphere_prod n (2 * S.card) hn) (S.val + S.val) (by simp; omega)
  simpa only [hm, hg, Multiset.card_add, Finset.card_val,
    show (S.card + S.card) / 2 = S.card by omega] using h

private lemma rhoD_pos_local (hn : 1 ≤ n) (i : ℕ) : 0 < rhoD n i := by
  unfold rhoD
  apply Finset.prod_pos
  intro t ht
  have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  positivity

private lemma mono_cont_local (b : Multiset (Fin n)) :
    Continuous (fun x : Fin n → ℝ => BstLean.Part36.monoVal x b) := by
  let β : Sym (Fin n) b.card := ⟨b, rfl⟩
  change Continuous (fun x => BstLean.Part36.monoVal x β.val)
  simp_rw [mono_enum β]
  fun_prop

private lemma Pcal_cont_local (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) :
    Continuous (Pcal k T Z) := by
  classical
  unfold Pcal uJ contr BstLean.Part36.mapMD
  apply continuous_finsetSum
  intro j hj
  apply Continuous.div_const
  apply continuous_finsetSum
  intro w hw
  apply Continuous.const_mul
  apply continuous_finsetProd
  intro t ht
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro β hβ
  exact (mono_cont_local β.val).const_mul _

private lemma mono_finset_mean (hn : 1 ≤ n) (S : Finset (Fin n)) (hS : S.Nonempty) :
    (∫ x, ∏ a ∈ S, x a ∂uniformSphere n) = 0 := by
  classical
  have h := (BstLean.Part36.sphere_multiset (uniformSphere n)
    (BstLean.Part33.uniformSphere_prod n S.card hn) S.val (by simp)).2
  obtain ⟨a, ha⟩ := hS
  have hc : S.val.count a = 1 := Multiset.count_eq_one_of_mem S.nodup ha
  have hz : BstLean.Part36.gpm S.val = 0 := by
    unfold BstLean.Part36.gpm
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    norm_num [hc, BstLean.Part29.gaussMom]
  simpa [BstLean.Part36.monoVal, hz] using h

private lemma mono_finset_orth (hn : 1 ≤ n) (S T : Finset (Fin n)) (hST : S ≠ T) :
    (∫ x, (∏ a ∈ S, x a) * (∏ a ∈ T, x a) ∂uniformSphere n) = 0 := by
  classical
  have h := (BstLean.Part36.sphere_multiset (uniformSphere n)
    (BstLean.Part33.uniformSphere_prod n (S.card + T.card) hn) (S.val + T.val) (by simp)).2
  have hex : ∃ a, (a ∈ S ∧ a ∉ T) ∨ (a ∈ T ∧ a ∉ S) := by
    by_contra hh
    push Not at hh
    apply hST
    ext a
    constructor
    · intro ha
      exact (hh a).1 ha
    · intro ha
      exact (hh a).2 ha
  obtain ⟨a, ha⟩ := hex
  have hc : (S.val + T.val).count a = 1 := by
    rcases ha with ha | ha
    · rw [Multiset.count_add, Multiset.count_eq_one_of_mem S.nodup ha.1,
        Multiset.count_eq_zero.mpr ha.2]
    · rw [Multiset.count_add, Multiset.count_eq_zero.mpr ha.2,
        Multiset.count_eq_one_of_mem T.nodup ha.1]
  have hz : BstLean.Part36.gpm (S.val + T.val) = 0 := by
    unfold BstLean.Part36.gpm
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    norm_num [hc, BstLean.Part29.gaussMom]
  simpa [BstLean.Part36.monoVal, Multiset.map_add, Multiset.prod_add, hz] using h

private lemma sqrt_triangle_finset {ι : Type*} (A : Finset ι) (u v : ι → ℝ) :
    Real.sqrt (∑ i ∈ A, (u i + v i) ^ 2) ≤
      Real.sqrt (∑ i ∈ A, u i ^ 2) + Real.sqrt (∑ i ∈ A, v i ^ 2) := by
  have hu : 0 ≤ ∑ i ∈ A, u i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hv : 0 ≤ ∑ i ∈ A, v i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hc := Real.sum_mul_le_sqrt_mul_sqrt A u v
  have he : (∑ i ∈ A, (u i + v i) ^ 2) =
      (∑ i ∈ A, u i ^ 2) + 2 * (∑ i ∈ A, u i * v i) + (∑ i ∈ A, v i ^ 2) := by
    simp_rw [add_sq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 2
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [he]
  nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv]

private lemma trace_symm_local {ι : Type*} [Fintype ι] {s l : ℕ}
    (A : (Fin (s + 2 * l) → ι) → ℝ) (hA : IsSymmT A) :
    IsSymmT (trL l A) := by
  classical
  intro σ w
  let e : Fin (s + 2 * l) ≃ Fin (2 * l) ⊕ Fin (s + 2 * l - 2 * l) :=
    (finCongr (by omega)).trans finSumFinEquiv.symm
  let τ : Equiv.Perm (Fin (s + 2 * l)) :=
    e.trans ((Equiv.sumCongr (Equiv.refl _) σ).trans e.symm)
  unfold trL
  apply Finset.sum_congr rfl
  intro c hc
  have hg : glue (s + 2 * l) l c (w ∘ σ) = glue (s + 2 * l) l c w ∘ τ := by
    funext t
    by_cases ht : t.val < 2 * l
    · have he : e t = Sum.inl ⟨t.val, ht⟩ := by
        dsimp [e, Equiv.trans_apply]
        convert finSumFinEquiv_symm_apply_castAdd (n := s + 2 * l - 2 * l)
          (⟨t.val, ht⟩ : Fin (2 * l)) using 1
        apply congrArg finSumFinEquiv.symm
        apply Fin.ext
        rfl
      have hτ : τ t = t := by
        change e.symm ((Equiv.sumCongr (Equiv.refl _) σ) (e t)) = t
        rw [he]
        simpa only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply] using
          (he ▸ e.symm_apply_apply t)
      simp [Function.comp_apply, hτ, glue, ht]
    · have he : e t = Sum.inr ⟨t.val - 2 * l, by have := t.isLt; omega⟩ := by
        dsimp [e, Equiv.trans_apply]
        convert finSumFinEquiv_symm_apply_natAdd (m := 2 * l)
          (⟨t.val - 2 * l, by have := t.isLt; omega⟩ : Fin (s + 2 * l - 2 * l)) using 1
        apply congrArg finSumFinEquiv.symm
        apply Fin.ext
        simp
        omega
      have hv : (τ t).val = 2 * l + (σ ⟨t.val - 2 * l, by have := t.isLt; omega⟩).val := by
        simp [τ, Equiv.trans_apply, he, e]
      have hτ : ¬ (τ t).val < 2 * l := by omega
      simp only [Function.comp_apply, glue, ht, hτ, dite_false]
      congr 1
      apply Fin.ext
      simp only [hv]
      omega
  rw [hg]
  exact hA τ _

/-- **Lemma `LF` (i)**, pathwise: `Var_x 𝒫(Z) ≥ (√P_α − √H_α)₊²`. -/
theorem LF_i (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) :
    max (Real.sqrt (Palpha k T Z) - Real.sqrt (Halpha k T Z)) 0 ^ 2 ≤ varU (uniformSphere n) (Pcal k T Z) := by
  classical
  let := BstLean.Part29.uniformSphere_isProbability n hn
  let A : Finset (Σ _ : ℕ, Finset (Fin n)) := (Finset.Icc 1 k).sigma
    (fun s => (Finset.univ : Finset (Fin n)).powersetCard (s * d))
  let φ : A → (Fin n → ℝ) → ℝ := fun i x =>
    (∏ a ∈ i.val.2, x a) * Real.sqrt (rhoD n i.val.2.card)
  have hc (i : A) : i.val.2.card = i.val.1 * d :=
    (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp i.property).2).2
  have hne (i : A) : i.val.2.Nonempty := by
    apply Finset.card_pos.mp
    rw [hc]
    exact Nat.mul_pos (Finset.mem_Icc.mp (Finset.mem_sigma.mp i.property).1).1 hd
  have hφc (i : A) : Continuous (φ i) := by dsimp [φ]; fun_prop
  have hnorm (i : A) : (∫ x, φ i x ^ 2 ∂uniformSphere n) = 1 := by
    have hp (x : Fin n → ℝ) : φ i x ^ 2 =
        rhoD n i.val.2.card * ∏ a ∈ i.val.2, x a ^ 2 := by
      simp only [φ, mul_pow, Real.sq_sqrt (rhoD_pos_local hn _).le, Finset.prod_pow]
      ring
    simp_rw [hp]
    rw [integral_const_mul, (squarefree_moment hn i.val.2).2]
    exact mul_one_div_cancel (rhoD_pos_local hn _).ne'
  have hmean (i : A) : (∫ x, φ i x ∂uniformSphere n) = 0 := by
    dsimp [φ]
    rw [integral_mul_const, mono_finset_mean hn _ (hne i), zero_mul]
  have horth (i j : A) (hij : i ≠ j) : (∫ x, φ i x * φ j x ∂uniformSphere n) = 0 := by
    have hsets : i.val.2 ≠ j.val.2 := by
      intro he
      apply hij
      apply Subtype.ext
      have hs : i.val.1 = j.val.1 := by
        apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < d)
        rw [← hc i, ← hc j, he]
      exact Sigma.ext hs (by simpa using he)
    have hp (x : Fin n → ℝ) : φ i x * φ j x =
        ((∏ a ∈ i.val.2, x a) * (∏ a ∈ j.val.2, x a)) *
          (Real.sqrt (rhoD n i.val.2.card) * Real.sqrt (rhoD n j.val.2.card)) := by
      dsimp [φ]; ring
    simp_rw [hp]
    rw [integral_mul_const, mono_finset_orth hn _ _ hsets, zero_mul]
  have hpcont := Pcal_cont_local k T Z
  have hb := BstLean.Part29.var_ge_bessel (uniformSphere n) (Pcal k T Z) φ 1
    (by norm_num) (sphere_integrable_local hn (hpcont.pow 2)) (sphere_integrable_local hn hpcont)
    (fun i j => sphere_integrable_local hn ((hφc i).mul (hφc j)))
    (fun i => sphere_integrable_local hn (hpcont.mul (hφc i)))
    (fun i => sphere_integrable_local hn (hφc i)) hmean horth hnorm
  have hcov (i : A) : (∫ x, Pcal k T Z x * φ i x ∂uniformSphere n) =
      wS k T i.val.2 Z := by
    dsimp [φ, wS]
    simp_rw [← mul_assoc]
    rw [integral_mul_const]
  simp only [hcov, div_one] at hb
  rw [Finset.sum_coe_sort A (fun i => wS k T i.2 Z ^ 2)] at hb
  let W : ℝ := ∑ i ∈ A, wS k T i.2 Z ^ 2 / (n : ℝ) ^ (k - i.1)
  have hW : W ≤ varU (uniformSphere n) (Pcal k T Z) := by
    apply le_trans _ hb
    apply Finset.sum_le_sum
    intro i hi
    have hnp : (1 : ℝ) ≤ (n : ℝ) ^ (k - i.1) := one_le_pow₀ (by exact_mod_cast hn)
    exact div_le_self (sq_nonneg _) hnp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let u : (Σ _ : ℕ, Finset (Fin n)) → ℝ := fun i =>
    wS k T i.2 Z / Real.sqrt ((n : ℝ) ^ (k - i.1))
  let v : (Σ _ : ℕ, Finset (Fin n)) → ℝ := fun i =>
    (qS (bEff n d k T i.1) i.2 Z - wS k T i.2 Z) / Real.sqrt ((n : ℝ) ^ (k - i.1))
  have hsq (a : ℝ) (i : Σ _ : ℕ, Finset (Fin n)) :
      (a / Real.sqrt ((n : ℝ) ^ (k - i.1))) ^ 2 = a ^ 2 / (n : ℝ) ^ (k - i.1) := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
  have hu : (∑ i ∈ A, u i ^ 2) = W := by simp only [u, W, hsq]
  have hv : (∑ i ∈ A, v i ^ 2) = Halpha k T Z := by
    dsimp [v]
    simp_rw [hsq, sub_sq_comm (qS _ _ Z)]
    dsimp [A]
    rw [Finset.sum_sigma]
    unfold Halpha
    simp_rw [Finset.sum_div]
  have huv : (∑ i ∈ A, (u i + v i) ^ 2) = Palpha k T Z := by
    have he (i : Σ _ : ℕ, Finset (Fin n)) : u i + v i =
        qS (bEff n d k T i.1) i.2 Z / Real.sqrt ((n : ℝ) ^ (k - i.1)) := by
      dsimp [u, v]; ring
    simp_rw [he, hsq]
    dsimp [A]
    rw [Finset.sum_sigma]
    unfold Palpha
    simp_rw [Finset.sum_div]
  have ht := sqrt_triangle_finset A u v
  rw [hu, hv, huv] at ht
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hmax : max (Real.sqrt (Palpha k T Z) - Real.sqrt (Halpha k T Z)) 0 ≤ Real.sqrt W := by
    apply max_le
    · linarith
    · positivity
  calc
    _ ≤ (Real.sqrt W) ^ 2 := pow_le_pow_left₀ (le_max_right _ _) hmax 2
    _ = W := Real.sq_sqrt hW0
    _ ≤ _ := hW

private lemma gaussian_product_moment_local {ι κ : Type*} [Fintype ι] [Fintype κ]
    (τ : κ → ι) : (∫ z, ∏ t, z (τ t) ∂stdGauss ι) =
      ∏ i, BstLean.Part29.gaussMom (Finset.univ.filter (fun t => τ t = i)).card := by
  classical
  have hp (z : ι → ℝ) : (∏ t, z (τ t)) =
      ∏ i, z i ^ (Finset.univ.filter (fun t => τ t = i)).card := by
    simpa using (Finset.prod_fiberwise' Finset.univ τ z).symm
  simp_rw [hp]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (f := fun (i : ι) (x : ℝ) =>
    x ^ (Finset.univ.filter (fun t => τ t = i)).card)]
  simp_rw [BstLean.Part29.gaussMom_eq]

private lemma injective_fiber_card_local {ι κ : Type*} [Fintype κ] (f : κ → ι)
    (hf : Function.Injective f) (i : ι) :
    (Finset.univ.filter (fun t => f t = i)).card = if ∃ t, f t = i then 1 else 0 := by
  classical
  by_cases hi : ∃ t, f t = i
  · obtain ⟨t, ht⟩ := hi
    have he : Finset.univ.filter (fun u => f u = i) = {t} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hu
        exact hf (hu.trans ht.symm)
      · rintro rfl
        exact ht
    rw [he, Finset.card_singleton, if_pos ⟨t, ht⟩]
  · have he : Finset.univ.filter (fun t => f t = i) = ∅ := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun ht => hi ⟨t, ht⟩
    rw [he, Finset.card_empty, if_neg hi]

private lemma gaussian_injective_products_local {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f g : κ → ι) (hf : Function.Injective f) (hg : Function.Injective g) :
    (∫ z, (∏ t, z (f t)) * (∏ t, z (g t)) ∂stdGauss ι) =
      if Set.range f = Set.range g then 1 else 0 := by
  classical
  have hp (z : ι → ℝ) : (∏ t, z (f t)) * (∏ t, z (g t)) =
      ∏ t : κ ⊕ κ, z (Sum.elim f g t) := by simp
  simp_rw [hp]
  rw [gaussian_product_moment_local]
  have hc (i : ι) : (Finset.univ.filter (fun t : κ ⊕ κ => Sum.elim f g t = i)).card =
      (if ∃ t, f t = i then 1 else 0) + (if ∃ t, g t = i then 1 else 0) := by
    rw [Finset.card_filter, Fintype.sum_sum_type]
    change (∑ t : κ, if f t = i then 1 else 0) + (∑ t : κ, if g t = i then 1 else 0) = _
    rw [← Finset.card_filter, ← Finset.card_filter,
      injective_fiber_card_local f hf, injective_fiber_card_local g hg]
  simp_rw [hc]
  by_cases he : Set.range f = Set.range g
  · rw [if_pos he]
    apply Finset.prod_eq_one
    intro i hi
    have hi' : (∃ t, f t = i) ↔ ∃ t, g t = i := by
      exact Set.ext_iff.mp he i
    by_cases h : ∃ t, f t = i <;> simp [h, ← hi', BstLean.Part29.gaussMom]
  · rw [if_neg he]
    have hex : ∃ i, ((∃ t, f t = i) ∧ ¬∃ t, g t = i) ∨
        ((∃ t, g t = i) ∧ ¬∃ t, f t = i) := by
      by_contra hh
      push Not at hh
      apply he
      ext i
      exact ⟨(hh i).1, (hh i).2⟩
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases hi with hi | hi <;> simp [hi.1, hi.2, BstLean.Part29.gaussMom]

private lemma gaussian_tensor_second_local {ι : Type*} [Fintype ι] {s : ℕ}
    (b : (Fin s → Fin n) → ℝ) (f : Fin s → Fin n → ι)
    (hf : Function.Injective (Function.uncurry f)) :
    (∫ Z, (∑ w, b w * ∏ t, Z (f t (w t))) ^ 2 ∂stdGauss ι) = frob b := by
  classical
  let U : (Fin s → Fin n) → (ι → ℝ) → ℝ := fun w Z => ∏ t, Z (f t (w t))
  have hu (w : Fin s → Fin n) : GaussianPoly (U w) := by
    apply gpoly_prod
    intro t ht
    exact gpoly_coord _
  have hInt (w v : Fin s → Fin n) : Integrable (fun Z => (b w * b v) * (U w Z * U v Z))
      (stdGauss ι) := gpoly_integrable (gpoly_mul (gpoly_const _) (gpoly_mul (hu w) (hu v)))
  have hinj (w : Fin s → Fin n) : Function.Injective (fun t => f t (w t)) := by
    intro t u h
    exact congrArg Prod.fst (@hf (t, w t) (u, w u) h)
  have hrange (w v : Fin s → Fin n) :
      Set.range (fun t => f t (w t)) = Set.range (fun t => f t (v t)) ↔ w = v := by
    constructor
    · intro h
      funext t
      have hh : f t (w t) ∈ Set.range (fun u => f u (v u)) := h ▸ Set.mem_range_self t
      obtain ⟨u, hu⟩ := hh
      have he := @hf (u, v u) (t, w t) hu
      have htu : u = t := congrArg Prod.fst he
      have hwv := congrArg Prod.snd he
      simpa [htu] using hwv.symm
    · rintro rfl
      rfl
  have hm (w v : Fin s → Fin n) : (∫ Z, U w Z * U v Z ∂stdGauss ι) = if w = v then 1 else 0 := by
    exact (gaussian_injective_products_local _ _ (hinj w) (hinj v)).trans (by simp only [hrange])
  have hex (Z : ι → ℝ) : (∑ w, b w * U w Z) ^ 2 =
      ∑ w, ∑ v, (b w * b v) * (U w Z * U v Z) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  change (∫ Z, (∑ w, b w * U w Z) ^ 2 ∂stdGauss ι) = _
  simp_rw [hex]
  rw [integral_finsetSum _ (fun w _ => integrable_finsetSum _ (fun v _ => hInt w v))]
  unfold frob
  apply Finset.sum_congr rfl
  intro w hw
  rw [integral_finsetSum _ (fun v _ => hInt w v)]
  simp_rw [integral_const_mul, hm]
  rw [Finset.sum_eq_single w]
  · simp [pow_two]
  · intro v hv hvw
    simp [Ne.symm hvw]
  · simp

private lemma parts_injective_local {s : ℕ} (hd : 1 ≤ d) (S : Finset (Fin n))
    (π : Fin s → Finset (Fin n)) (hπ : π ∈ parts d s S) : Function.Injective π := by
  classical
  have hp := (Finset.mem_filter.mp hπ).2
  intro t u he
  by_contra htu
  have hdis := hp.2.1 t u htu
  rw [← he] at hdis
  have hz : π t = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact Finset.disjoint_left.mp hdis ha ha
  have hc := hp.1 t
  rw [hz, Finset.card_empty] at hc
  omega

private lemma parts_perm_local {s : ℕ} (S : Finset (Fin n))
    (π : Fin s → Finset (Fin n)) (hπ : π ∈ parts d s S) (σ : Equiv.Perm (Fin s)) :
    π ∘ σ ∈ parts d s S := by
  classical
  have hp := (Finset.mem_filter.mp hπ).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, (fun t => hp.1 (σ t)), ?_, ?_⟩
  · intro t u htu
    exact hp.2.1 (σ t) (σ u) (fun h => htu (σ.injective h))
  · rw [← hp.2.2]
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨σ t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨σ.symm t, by simpa using ht⟩

private lemma contr_perm_local {s : ℕ} (b : (Fin s → Fin n) → ℝ) (hb : IsSymmT b)
    (v : Fin s → Fin n → ℝ) (σ : Equiv.Perm (Fin s)) :
    contr b (v ∘ σ) = contr b v := by
  classical
  let e : (Fin s → Fin n) ≃ (Fin s → Fin n) :=
    Equiv.arrowCongr σ.symm (Equiv.refl _)
  unfold contr
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro w hw
  have hb' : b (e w) = b w := hb σ w
  rw [hb']
  change b w * (∏ t, v (σ t) (w (σ t))) = _
  exact congrArg (fun x => b w * x) (Equiv.prod_comp σ (fun t => v t (w t)))

private def pureIndex_local (β : Finset (Fin n)) (hβ : β.card = d) (a : Fin n) : CoefIdxD n d :=
  ⟨Fin.last d, (⟨β.val, hβ⟩, a)⟩

private lemma pureIndex_block_local {β γ : Finset (Fin n)} {hβ : β.card = d} {hγ : γ.card = d}
    {a c : Fin n} (h : pureIndex_local β hβ a = pureIndex_local γ hγ c) : β = γ := by
  exact Finset.val_injective (congrArg (fun z : CoefIdxD n d => z.2.1.val) h)

private lemma pureIndex_output_local {β γ : Finset (Fin n)} {hβ : β.card = d} {hγ : γ.card = d}
    {a c : Fin n} (h : pureIndex_local β hβ a = pureIndex_local γ hγ c) : a = c := by
  exact congrArg (fun z : CoefIdxD n d => z.2.2) h

private lemma contr_cols_gpoly_local {s : ℕ} (b : (Fin s → Fin n) → ℝ)
    (π : Fin s → Finset (Fin n)) : GaussianPoly (fun Z => contr b (fun t => colP (d := d) Z (π t))) := by
  unfold contr
  apply gpoly_sum
  intro w hw
  apply gpoly_mul (gpoly_const _)
  apply gpoly_prod
  intro t ht
  unfold colP
  dsimp only
  split_ifs
  · exact gpoly_coord _
  · exact gpoly_const 0

private lemma partition_contr_second_local {s : ℕ} (hd : 1 ≤ d) (S : Finset (Fin n))
    (π : Fin s → Finset (Fin n)) (hπ : π ∈ parts d s S) (b : (Fin s → Fin n) → ℝ) :
    (∫ Z, contr b (fun t => colP Z (π t)) ^ 2 ∂stdGauss (CoefIdxD n d)) = frob b := by
  classical
  have hcard := (Finset.mem_filter.mp hπ).2.1
  let f : Fin s → Fin n → CoefIdxD n d := fun t a => pureIndex_local (π t) (hcard t) a
  have hf : Function.Injective (Function.uncurry f) := by
    intro p q h
    apply Prod.ext
    · exact parts_injective_local hd S π hπ (pureIndex_block_local h)
    · exact pureIndex_output_local h
  have he (Z : CoefIdxD n d → ℝ) : contr b (fun t => colP Z (π t)) =
      ∑ w, b w * ∏ t, Z (f t (w t)) := by
    unfold contr
    simp only [colP, dif_pos (hcard _), f, pureIndex_local]
  simp_rw [he]
  exact gaussian_tensor_second_local b f hf

private lemma partition_contr_orth_local {s : ℕ} (hd : 1 ≤ d) (S : Finset (Fin n))
    (π π' : Fin s → Finset (Fin n)) (hπ : π ∈ parts d s S) (hπ' : π' ∈ parts d s S)
    (b : (Fin s → Fin n) → ℝ) (hr : Set.range π ≠ Set.range π') :
    (∫ Z, contr b (fun t => colP Z (π t)) * contr b (fun t => colP Z (π' t))
      ∂stdGauss (CoefIdxD n d)) = 0 := by
  classical
  have hc := (Finset.mem_filter.mp hπ).2.1
  have hc' := (Finset.mem_filter.mp hπ').2.1
  let f : (Fin s → Fin n) → Fin s → CoefIdxD n d := fun w t => pureIndex_local (π t) (hc t) (w t)
  let g : (Fin s → Fin n) → Fin s → CoefIdxD n d := fun w t => pureIndex_local (π' t) (hc' t) (w t)
  let U : (Fin s → Fin n) → (CoefIdxD n d → ℝ) → ℝ := fun w Z => ∏ t, Z (f w t)
  let V : (Fin s → Fin n) → (CoefIdxD n d → ℝ) → ℝ := fun w Z => ∏ t, Z (g w t)
  have hf (w : Fin s → Fin n) : Function.Injective (f w) := by
    intro t u h
    exact parts_injective_local hd S π hπ (pureIndex_block_local h)
  have hg (w : Fin s → Fin n) : Function.Injective (g w) := by
    intro t u h
    exact parts_injective_local hd S π' hπ' (pureIndex_block_local h)
  have hneq (w v : Fin s → Fin n) : Set.range (f w) ≠ Set.range (g v) := by
    intro he
    apply hr
    ext β
    constructor
    · rintro ⟨t, rfl⟩
      have hh : f w t ∈ Set.range (g v) := he ▸ Set.mem_range_self t
      obtain ⟨u, hu⟩ := hh
      exact ⟨u, pureIndex_block_local hu⟩
    · rintro ⟨t, rfl⟩
      have hh : g v t ∈ Set.range (f w) := he.symm ▸ Set.mem_range_self t
      obtain ⟨u, hu⟩ := hh
      exact ⟨u, pureIndex_block_local hu⟩
  have hm (w v : Fin s → Fin n) : (∫ Z, U w Z * V v Z ∂stdGauss (CoefIdxD n d)) = 0 := by
    simpa only [U, V, ite_eq_right (hneq w v)] using gaussian_injective_products_local (f w) (g v) (hf w) (hg v)
  have hu (w : Fin s → Fin n) : GaussianPoly (U w) := by
    apply gpoly_prod; intro t ht; exact gpoly_coord _
  have hv (w : Fin s → Fin n) : GaussianPoly (V w) := by
    apply gpoly_prod; intro t ht; exact gpoly_coord _
  have hInt (w v : Fin s → Fin n) : Integrable (fun Z => (b w * b v) * (U w Z * V v Z))
      (stdGauss (CoefIdxD n d)) := gpoly_integrable (gpoly_mul (gpoly_const _) (gpoly_mul (hu w) (hv v)))
  have hex (Z : CoefIdxD n d → ℝ) :
      contr b (fun t => colP Z (π t)) * contr b (fun t => colP Z (π' t)) =
        ∑ w, ∑ v, (b w * b v) * (U w Z * V v Z) := by
    unfold contr
    simp only [colP, dite_eq_left (hc _), dite_eq_left (hc' _)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp [U, V, f, g, pureIndex_local]
    ring
  simp_rw [hex]
  rw [integral_finsetSum _ (fun w _ => integrable_finsetSum _ (fun v _ => hInt w v))]
  apply Finset.sum_eq_zero
  intro w hw
  rw [integral_finsetSum _ (fun v _ => hInt w v)]
  simp_rw [integral_const_mul, hm, mul_zero]
  simp

private lemma same_range_perm_local {ι : Type*} {s : ℕ} (f g : Fin s → ι)
    (hf : Function.Injective f) (hg : Function.Injective g) (h : Set.range f = Set.range g) :
    ∃ σ : Equiv.Perm (Fin s), g = f ∘ σ := by
  let ef := Equiv.ofInjective f hf
  let eg := Equiv.ofInjective g hg
  let σ : Equiv.Perm (Fin s) := eg.trans ((Set.equivOfEq h.symm).trans ef.symm)
  refine ⟨σ, ?_⟩
  funext t
  exact (congrArg Subtype.val (ef.apply_symm_apply ((Set.equivOfEq h.symm) (eg t)))).symm

private lemma partition_matching_card_local {s : ℕ} (hd : 1 ≤ d) (S : Finset (Fin n))
    (π : Fin s → Finset (Fin n)) (hπ : π ∈ parts d s S) :
    ((parts d s S).filter (fun π' => Set.range π = Set.range π')).card = s.factorial := by
  classical
  let F : Equiv.Perm (Fin s) → (Fin s → Finset (Fin n)) := fun σ => π ∘ σ
  have hF : Function.Injective F := by
    intro σ τ he
    apply Equiv.ext
    intro t
    exact parts_injective_local hd S π hπ (congrFun he t)
  have hr (σ : Equiv.Perm (Fin s)) : Set.range π = Set.range (F σ) := by
    ext a
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨σ.symm t, by simp [F]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨σ t, rfl⟩
  have he : (parts d s S).filter (fun π' => Set.range π = Set.range π') = Finset.univ.image F := by
    ext π'
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hπ', he⟩
      obtain ⟨σ, hσ⟩ := same_range_perm_local π π' (parts_injective_local hd S π hπ)
        (parts_injective_local hd S π' hπ') he
      exact ⟨σ, hσ.symm⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨parts_perm_local S π hπ σ, hr σ⟩
  rw [he, Finset.card_image_of_injective _ hF, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

private lemma qS_second_local {s : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (S : Finset (Fin n)) (hS : S.card = s * d) (b : (Fin s → Fin n) → ℝ) (hb : IsSymmT b) :
    (∫ Z, qS b S Z ^ 2 ∂stdGauss (CoefIdxD n d)) =
      (parts d s S).card * (s.factorial : ℝ) * frob b / rhoD n (s * d) := by
  classical
  let C : (Fin s → Finset (Fin n)) → (CoefIdxD n d → ℝ) → ℝ :=
    fun π Z => contr b (fun t => colP Z (π t))
  have hInt (π π' : Fin s → Finset (Fin n)) : Integrable (fun Z => C π Z * C π' Z)
      (stdGauss (CoefIdxD n d)) := gpoly_integrable
    (gpoly_mul (contr_cols_gpoly_local b π) (contr_cols_gpoly_local b π'))
  have hcov (π π' : Fin s → Finset (Fin n)) (hπ : π ∈ parts d s S) (hπ' : π' ∈ parts d s S) :
      (∫ Z, C π Z * C π' Z ∂stdGauss (CoefIdxD n d)) = if Set.range π = Set.range π' then frob b else 0 := by
    by_cases he : Set.range π = Set.range π'
    · rw [ite_eq_left he]
      obtain ⟨σ, hσ⟩ := same_range_perm_local π π' (parts_injective_local hd S π hπ)
        (parts_injective_local hd S π' hπ') he
      have heq (Z : CoefIdxD n d → ℝ) : C π' Z = C π Z := by
        rw [hσ]
        exact contr_perm_local b hb (fun t => colP Z (π t)) σ
      simp_rw [heq, ← pow_two]
      exact partition_contr_second_local hd S π hπ b
    · rw [ite_eq_right he]
      exact partition_contr_orth_local hd S π π' hπ hπ' b he
  have hex (Z : CoefIdxD n d → ℝ) : qS b S Z ^ 2 =
      (Real.sqrt (rhoD n (s * d)))⁻¹ ^ 2 *
        ∑ π ∈ parts d s S, ∑ π' ∈ parts d s S, C π Z * C π' Z := by
    unfold qS
    rw [mul_pow]
    conv_lhs => arg 2; rw [pow_two, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro π hπ
    rw [Finset.mul_sum]
  simp_rw [hex]
  rw [integral_const_mul, integral_finsetSum _ (fun π _ =>
    integrable_finsetSum _ (fun π' _ => hInt π π'))]
  have he : (∑ π ∈ parts d s S, ∫ Z, ∑ π' ∈ parts d s S, C π Z * C π' Z ∂stdGauss (CoefIdxD n d)) =
      (parts d s S).card * ((s.factorial : ℝ) * frob b) := by
    trans ∑ π ∈ parts d s S, (s.factorial : ℝ) * frob b
    · apply Finset.sum_congr rfl
      intro π hπ
      rw [integral_finsetSum _ (fun π' _ => hInt π π')]
      have heq : (∑ π' ∈ parts d s S, ∫ Z, C π Z * C π' Z ∂stdGauss (CoefIdxD n d)) =
          ∑ π' ∈ parts d s S, if Set.range π = Set.range π' then frob b else 0 := by
        apply Finset.sum_congr rfl
        intro π' hπ'
        exact hcov π π' hπ hπ'
      rw [heq, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, partition_matching_card_local hd S π hπ]
    · simp
  rw [he, inv_pow, Real.sq_sqrt (rhoD_pos_local hn _).le]
  ring

private lemma parts_cons_local {s : ℕ} (S β : Finset (Fin n))
    (π : Fin s → Finset (Fin n)) :
    Fin.cons β π ∈ parts d (s + 1) S ↔
      β ∈ S.powersetCard d ∧ π ∈ parts d s (S \ β) := by
  classical
  simp only [parts, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨hc, hdis, hu⟩
    have hβ : β ⊆ S := by
      intro a ha
      rw [← hu]
      exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, ha⟩
    refine ⟨⟨hβ, hc 0⟩, (fun t => hc t.succ), ?_, ?_⟩
    · intro t u htu
      exact hdis t.succ u.succ (fun he => htu (Fin.succ_injective _ he))
    · ext a
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · rintro ⟨t, ht⟩
        refine ⟨?_, ?_⟩
        · rw [← hu]
          exact Finset.mem_biUnion.mpr ⟨t.succ, Finset.mem_univ _, ht⟩
        · exact fun ha => Finset.disjoint_left.mp (hdis 0 t.succ (by
            intro he; have := congrArg Fin.val he; simp at this)) ha ht
      · rintro ⟨ha, hnot⟩
        rw [← hu] at ha
        obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp ha
        refine Fin.cases ?_ (fun u hu => ⟨u, hu⟩) t ht
        exact fun ht => (hnot ht).elim
  · rintro ⟨⟨hβ, hcβ⟩, hc, hdis, hu⟩
    refine ⟨?_, ?_, ?_⟩
    · exact Fin.cases hcβ hc
    · intro t u htu
      refine Fin.cases ?_ ?_ t u htu
      · intro u htu
        refine Fin.cases (fun he => (he rfl).elim) ?_ u htu
        intro v _
        apply Finset.disjoint_left.mpr
        intro a ha hv
        have : a ∈ S \ β := by
          rw [← hu]
          exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hv⟩
        exact (Finset.mem_sdiff.mp this).2 ha
      · intro v u htu
        refine Fin.cases ?_ ?_ u htu
        · intro _
          apply Finset.disjoint_left.mpr
          intro a hv ha
          have : a ∈ S \ β := by
            rw [← hu]
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hv⟩
          exact (Finset.mem_sdiff.mp this).2 ha
        · intro w hne
          exact hdis v w (fun he => hne (congrArg Fin.succ he))
    · ext a
      constructor
      · intro ha
        obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp ha
        refine Fin.cases (fun hb => hβ hb) ?_ t ht
        intro u hu'
        have : a ∈ S \ β := by
          rw [← hu]
          exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hu'⟩
        exact (Finset.mem_sdiff.mp this).1
      · intro ha
        by_cases hb : a ∈ β
        · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, hb⟩
        · have : a ∈ S \ β := Finset.mem_sdiff.mpr ⟨ha, hb⟩
          rw [← hu] at this
          obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp this
          exact Finset.mem_biUnion.mpr ⟨t.succ, Finset.mem_univ _, ht⟩

private lemma parts_card_succ_local {s : ℕ} (S : Finset (Fin n)) :
    (parts d (s + 1) S).card = ∑ β ∈ S.powersetCard d, (parts d s (S \ β)).card := by
  classical
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun π _ => ⟨π 0, Fin.tail π⟩)
  · intro π hπ
    rw [Finset.mem_sigma]
    exact (parts_cons_local S (π 0) (Fin.tail π)).mp (by simpa using hπ)
  · intro π hπ π' hπ' he
    have hh : π 0 = π' 0 := congrArg Sigma.fst he
    have ht : Fin.tail π = Fin.tail π' := by
      exact congrArg (fun p : Σ _ : Finset (Fin n), Fin s → Finset (Fin n) => p.2) he
    rw [← Fin.cons_self_tail π, ← Fin.cons_self_tail π', hh, ht]
  · intro p hp
    refine ⟨Fin.cons p.1 p.2, ?_, ?_⟩
    · exact (parts_cons_local S p.1 p.2).mpr (Finset.mem_sigma.mp hp)
    · simp

private lemma parts_card_factorial_local (s : ℕ) (S : Finset (Fin n))
    (hS : S.card = s * d) :
    (parts d s S).card * d.factorial ^ s = (s * d).factorial := by
  classical
  induction s generalizing S with
  | zero =>
    have he : S = ∅ := Finset.card_eq_zero.mp (by simpa using hS)
    subst S
    simp [parts]
  | succ s ih =>
    rw [parts_card_succ_local, pow_succ, ← Nat.mul_assoc, Finset.sum_mul]
    have he : (∑ β ∈ S.powersetCard d, (parts d s (S \ β)).card * d.factorial ^ s) =
        (S.card.choose d) * (s * d).factorial := by
      trans ∑ β ∈ S.powersetCard d, (s * d).factorial
      · apply Finset.sum_congr rfl
        intro β hβ
        obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hβ
        apply ih
        rw [Finset.card_sdiff_of_subset hsub, hS, hcard, Nat.succ_mul]
        omega
      · simp [Finset.card_powersetCard]
    rw [he, hS]
    have hh := Nat.choose_mul_factorial_mul_factorial
      (show d ≤ (s + 1) * d by rw [Nat.add_mul]; omega)
    have hsub : (s + 1) * d - d = s * d := by rw [Nat.add_mul]; omega
    rw [hsub] at hh
    nlinarith

private lemma total_parts_card_local (s : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d), (parts d s S).card) *
      d.factorial ^ s = n.descFactorial (s * d) := by
  classical
  rw [Finset.sum_mul]
  trans ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d), (s * d).factorial
  · apply Finset.sum_congr rfl
    intro S hS
    exact parts_card_factorial_local s S (Finset.mem_powersetCard.mp hS).2
  · simp [Finset.card_powersetCard, Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]

private lemma falling_prod_local (n p : ℕ) :
    (∏ i ∈ Finset.range p, ((n : ℝ) - i)) = (n.descFactorial p : ℝ) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ, Nat.cast_mul]
    by_cases hp : p ≤ n
    · rw [Nat.cast_sub hp]
      ring
    · have hz : n.descFactorial p = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp [hz]

/-- **Lemma `LC-mean`**: `E Σ_{|S| = sd} q_S[b]² = λ_{n,s} s! ‖b‖² / (d!)^s` for symmetric `b`. -/
theorem LC_mean (hn : 1 ≤ n) (hd : 1 ≤ d) (s : ℕ) (hs : 1 ≤ s) (b : (Fin s → Fin n) → ℝ) (hb : IsSymmT b) :
    Integrable (fun Z => ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d), qS b S Z ^ 2)
      (stdGauss (CoefIdxD n d)) ∧
    ∫ Z, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d), qS b S Z ^ 2 ∂stdGauss (CoefIdxD n d) =
      lamS n d s * (s.factorial : ℝ) * frob b / (d.factorial : ℝ) ^ s := by
  refine ⟨qSquares_integrable b, ?_⟩
  classical
  rw [integral_finsetSum _ (fun S _ => gpoly_integrable (gpoly_pow (qS_gpoly b S) 2))]
  have he : (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d),
      ∫ Z, qS b S Z ^ 2 ∂stdGauss (CoefIdxD n d)) =
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d),
        ((parts d s S).card : ℝ)) * (s.factorial : ℝ) * frob b / rhoD n (s * d) := by
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S hS
    simpa only [div_eq_mul_inv] using qS_second_local hn hd S (Finset.mem_powersetCard.mp hS).2 b hb
  rw [he]
  have hc := congrArg (fun a : ℕ => (a : ℝ)) (total_parts_card_local (n := n) (d := d) s)
  simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow] at hc
  have hfac : (d.factorial : ℝ) ^ s ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero d)
  have hρ : rhoD n (s * d) ≠ 0 := ne_of_gt (rhoD_pos_local hn _)
  have hlam : lamS n d s = (n.descFactorial (s * d) : ℝ) / rhoD n (s * d) := by
    unfold lamS rhoD
    rw [Finset.prod_div_distrib, falling_prod_local]
  rw [hlam]
  field_simp
  linear_combination frob b * hc

/-- `ν_{s,0} = 1` and `0 ≤ ν_{s,l} ≤ (d+1)^l` (`sd ≤ n`). -/
theorem nu_bounds (hn : 1 ≤ n) (s l : ℕ) (hsd : s * d ≤ n) :
    nuC n d s 0 = 1 ∧ 0 ≤ nuC n d s l ∧ nuC n d s l ≤ ((d : ℝ) + 1) ^ l := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun a => a.val < s * d)
  have hcard : S.card = s * d := by
    let e : Fin (s * d) ↪ Fin n := ⟨Fin.castLE hsd, Fin.castLE_injective hsd⟩
    have he : S = Finset.univ.map e := by
      ext a
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro ha
        exact ⟨⟨a.val, ha⟩, Fin.ext rfl⟩
      · rintro ⟨b, rfl⟩
        exact b.isLt
    rw [he, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  let W : (Fin n → ℝ) → ℝ := fun x => ∏ a ∈ S, x a ^ 2
  have hW (x : Fin n → ℝ) :
      (∏ a : Fin n, if a.val < s * d then x a ^ 2 else 1) = W x := by
    exact (Finset.prod_filter (fun a : Fin n => a.val < s * d) _).symm
  have hW0 (x : Fin n → ℝ) : 0 ≤ W x := Finset.prod_nonneg (fun a _ => sq_nonneg _)
  have hWc : Continuous W := by unfold W; fun_prop
  have hWi := (squarefree_moment hn S).1
  have hWm : (∫ x, W x ∂uniformSphere n) = 1 / rhoD n (s * d) := by
    simpa only [W, hcard] using (squarefree_moment hn S).2
  have hr := rhoD_pos_local hn (s * d)
  have hF : Integrable (fun x => phiSq d x ^ l * W x) (uniformSphere n) :=
    sphere_integrable_local hn ((phiSq_cont.pow l).mul hWc)
  have hnon : 0 ≤ ∫ x, phiSq d x ^ l * W x ∂uniformSphere n := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (pow_nonneg (Finset.sum_nonneg (fun p _ => sq_nonneg _)) l) (hW0 x)
  have hup : (∫ x, phiSq d x ^ l * W x ∂uniformSphere n) ≤
      ((d : ℝ) + 1) ^ l * (1 / rhoD n (s * d)) := by
    rw [← hWm, ← integral_const_mul]
    apply integral_mono_ae hF (hWi.const_mul _)
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ => sq_nonneg _)) (phiSq_le x hx) l) (hW0 x)
  unfold nuC
  simp_rw [hW]
  refine ⟨?_, mul_nonneg hnon hr.le, ?_⟩
  · simp only [pow_zero, one_mul, hWm]
    exact one_div_mul_cancel hr.ne'
  · calc
      _ ≤ (((d : ℝ) + 1) ^ l * (1 / rhoD n (s * d))) * rhoD n (s * d) :=
        mul_le_mul_of_nonneg_right hup hr.le
      _ = ((d : ℝ) + 1) ^ l := by rw [mul_assoc, one_div_mul_cancel hr.ne', mul_one]

/-- The effective tensors are symmetric. -/
theorem bEff_symm (k : ℕ) (T : Tens n) (hT : TSymm k T) (s : ℕ) : IsSymmT (bEff n d k T s) := by
  classical
  intro σ w
  unfold bEff
  apply Finset.sum_congr rfl
  intro l hl
  have hlk := (Finset.mem_filter.mp hl).2
  by_cases hs : s = 0
  · subst s
    congr 2
    funext t
    exact Fin.elim0 (show Fin 0 from ⟨t.val, by have := t.isLt; omega⟩)
  · have hsym := trace_symm_local (T (s + 2 * l)) (hT _ (by omega) hlk)
    let e : Fin (s + 2 * l - 2 * l) ≃ Fin s := finCongr (by omega)
    have heq : (fun t : Fin (s + 2 * l - 2 * l) => (w ∘ σ) ⟨t.val, by have := t.isLt; omega⟩) =
        (fun t : Fin (s + 2 * l - 2 * l) => w ⟨t.val, by have := t.isLt; omega⟩) ∘
        ((e.trans σ).trans e.symm) := by
      funext t
      rfl
    unfold aT
    rw [heq, hsym]

private lemma trace_frob_le_local {ι : Type*} [Fintype ι] {j : ℕ} (l : ℕ)
    (hl : 2 * l ≤ j) (A : (Fin j → ι) → ℝ) :
    frob (trL l A) ≤ (Fintype.card ι : ℝ) ^ l * frob A := by
  classical
  let G : (Fin l → ι) × (Fin (j - 2 * l) → ι) → (Fin j → ι) :=
    fun p => glue j l p.1 p.2
  have hinj : Function.Injective G := by
    intro p q h
    apply Prod.ext
    · funext t
      have h' := congrFun h ⟨2 * t.val, by omega⟩
      simpa [G, glue, show 2 * t.val < 2 * l by omega] using h'
    · funext t
      have h' := congrFun h ⟨2 * l + t.val, by omega⟩
      simpa [G, glue, show ¬2 * l + t.val < 2 * l by omega] using h'
  have hsum : (∑ w, ∑ c, A (glue j l c w) ^ 2) ≤ frob A := by
    rw [Finset.sum_comm]
    change (∑ c, ∑ w, A (G (c, w)) ^ 2) ≤ frob A
    rw [← Fintype.sum_prod_type (fun p => A (G p) ^ 2)]
    calc
      _ = ∑ v ∈ Finset.univ.image G, A v ^ 2 := by
        rw [Finset.sum_image (fun p _ q _ h => hinj h)]
      _ ≤ frob A := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  unfold frob trL
  calc
    _ ≤ ∑ w, (Fintype.card ι : ℝ) ^ l * ∑ c, A (glue j l c w) ^ 2 := by
      apply Finset.sum_le_sum
      intro w hw
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : Fin l → ι => (1 : ℝ)) (fun c => A (glue j l c w))
      simpa using h
    _ = (Fintype.card ι : ℝ) ^ l * ∑ w, ∑ c, A (glue j l c w) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

private lemma trL_zero_local {j : ℕ} (A : (Fin j → Fin n) → ℝ) : trL 0 A = A := by
  funext w
  simp only [trL, Finset.univ_unique, Finset.sum_singleton]
  congr 1

private lemma aSq_zero_local (T : Tens n) (j : ℕ) :
    aSq n d T j 0 = frob (T j) / DD n d ^ j := by
  simp [aSq, trL_zero_local, cQ, Nat.factorial_ne_zero]
  ring

private lemma aT_frob_local (T : Tens n) (j l : ℕ) :
    frob (aT n d T j l) = aSq n d T j l := by
  classical
  have hp : (Real.sqrt (DD n d) ^ j) ^ 2 = DD n d ^ j := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, Real.sq_sqrt (by unfold DD; positivity)]
  unfold frob aT aSq
  simp only [mul_pow, div_pow, hp]
  rw [← Finset.mul_sum]
  rfl

private lemma aSq_trace_le_local (T : Tens n) (j l : ℕ) (hl : 2 * l ≤ j) :
    aSq n d T j l ≤ (cQ j l : ℝ) ^ 2 * (n : ℝ) ^ l * aSq n d T j 0 := by
  have h := trace_frob_le_local l hl (T j)
  simp only [Fintype.card_fin] at h
  rw [aSq_zero_local]
  unfold aSq
  have hD : 0 ≤ DD n d := by unfold DD; positivity
  have hh := mul_le_mul_of_nonneg_left h
    (by positivity : 0 ≤ (cQ j l : ℝ) ^ 2 / DD n d ^ j)
  convert hh using 1 <;> ring

private lemma weighted_trace_le_local (hn : 1 ≤ n) (k : ℕ) (T : Tens n) (j l : ℕ)
    (hj : j ∈ Finset.Icc 1 k) (hl : 2 * l ≤ j) (C : ℝ) (hC : 0 ≤ C) :
    C * aSq n d T j l / (n : ℝ) ^ (k - (j - 2 * l)) ≤
      (C * (cQ j l : ℝ) ^ 2 / ((j.factorial : ℝ) * j * (n : ℝ) ^ l)) * tj n d k T j := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hj
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hfac : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have he : k - (j - 2 * l) = (k - j) + l + l := by omega
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (aSq_trace_le_local (d := d) T j l hl) hC)
    (by positivity : 0 ≤ (n : ℝ) ^ (k - (j - 2 * l)))
  refine hh.trans_eq ?_
  rw [he, pow_add, pow_add]
  unfold tj
  field_simp
  <;> ring

private lemma maxJ_nonneg_local (k : ℕ) (g : ℕ → ℝ) : 0 ≤ maxJ k g := by
  unfold maxJ
  generalize ((List.range' 1 k).map g) = xs
  induction xs with
  | nil => simp
  | cons x xs ih => exact le_trans ih (le_max_right _ _)

private lemma le_maxJ_local (k : ℕ) (g : ℕ → ℝ) (j : ℕ) (hj : j ∈ Finset.Icc 1 k) :
    g j ≤ maxJ k g := by
  have hm : g j ∈ (List.range' 1 k).map g := by
    apply List.mem_map.mpr
    refine ⟨j, ?_, rfl⟩
    simpa using (show 1 ≤ j ∧ j < 1 + k from
      ⟨(Finset.mem_Icc.mp hj).1, by have := (Finset.mem_Icc.mp hj).2; omega⟩)
  unfold maxJ
  generalize ((List.range' 1 k).map g) = xs at *
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    rcases List.mem_cons.mp hm with h | h
    · simpa [h] using le_max_left x (xs.foldr max 0)
    · exact (ih h).trans (le_max_right _ _)

private lemma frob_cast_local (s l : ℕ) (A : (Fin (s + 2 * l - 2 * l) → Fin n) → ℝ) :
    frob (fun w : Fin s → Fin n => A (fun t => w ⟨t.val, by have := t.isLt; omega⟩)) = frob A := by
  classical
  let e : (Fin s → Fin n) ≃ (Fin (s + 2 * l - 2 * l) → Fin n) :=
    Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl _)
  exact e.sum_comp (fun w => A w ^ 2)

private lemma frob_sum_error_local {ι : Type*} [Fintype ι] {a : ℕ} (η : ℝ) (hη : 0 < η)
    (L : Finset ℕ) (A B : (Fin a → ι) → ℝ) (C : ℕ → (Fin a → ι) → ℝ)
    (hA : ∀ w, A w = B w - ∑ l ∈ L, C l w) :
    frob A ≤ (1 + η) * frob B + (1 + 1 / η) * L.card * ∑ l ∈ L, frob (C l) := by
  classical
  have hy (b r : ℝ) : (b - r) ^ 2 ≤ (1 + η) * b ^ 2 + (1 + 1 / η) * r ^ 2 := by
    apply (mul_le_mul_iff_right₀ hη).mp
    have he : η * (1 + 1 / η) = η + 1 := by field_simp
    rw [mul_add, ← mul_assoc η (1 + 1 / η), he]
    nlinarith only [sq_nonneg (η * b + r)]
  unfold frob
  calc
    _ ≤ ∑ w, ((1 + η) * B w ^ 2 + (1 + 1 / η) * (L.card : ℝ) * (∑ l ∈ L, C l w ^ 2)) := by
      apply Finset.sum_le_sum
      intro w hw
      rw [hA]
      have hc := Finset.sum_mul_sq_le_sq_mul_sq L (fun _ => (1 : ℝ)) (fun l => C l w)
      simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
      have hh := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 1 + 1 / η)
      have hh' : (1 + 1 / η) * (∑ l ∈ L, C l w) ^ 2 ≤
          (1 + 1 / η) * (L.card : ℝ) * (∑ l ∈ L, C l w ^ 2) := by
        convert hh using 1 <;> ring
      exact (hy _ _).trans (add_le_add le_rfl hh')
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]

private lemma cascade_reindex_local (k : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ s ∈ Finset.Icc 1 k, ∑ l ∈ Finset.Icc 1 (Ls k s), F s l) =
      ∑ j ∈ Finset.Icc 1 k, ∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j),
        F (j - 2 * l) l := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun (i : Σ _ : ℕ, ℕ) _ => (⟨i.1 + 2 * i.2, i.2⟩ : Σ _ : ℕ, ℕ))
  · intro i hi
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, Ls] at *
    omega
  · intro i hi i' hi' he
    cases i with
    | mk s l =>
      cases i' with
      | mk s' l' =>
        have h1 := congrArg Sigma.fst he
        have h2 := congrArg (fun x : Σ _ : ℕ, ℕ => x.2) he
        dsimp only at h1 h2
        congr 1 <;> omega
  · intro i hi
    refine ⟨⟨i.1 - 2 * i.2, i.2⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, Ls] at *
      omega
    · have hi' := hi
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hi'
      apply Sigma.ext (by dsimp only; omega)
      rfl
  · intro i hi
    change F i.1 i.2 = F (i.1 + 2 * i.2 - 2 * i.2) i.2
    simp only [Nat.add_sub_cancel_right]

private lemma tj_nonneg_local (k : ℕ) (T : Tens n) (j : ℕ) : 0 ≤ tj n d k T j := by
  unfold tj aSq frob
  have hD : 0 ≤ DD n d := by unfold DD; positivity
  positivity

private lemma Nn_trace_bound_local (hn : 1 ≤ n) (k : ℕ) (T : Tens n) :
    Nn n d k T ≤ rhoBar n k * ∑ j ∈ Finset.Icc 1 k, tj n d k T j := by
  classical
  have hex : Nn n d k T = ∑ j ∈ Finset.Icc 1 k,
      ∑ l ∈ (Finset.range (k + 1)).filter (fun l => 2 * l < j),
        ((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * 4 ^ l * aSq n d T j l /
          (n : ℝ) ^ (k - (j - 2 * l)) := by
    simp only [Nn, levels, Finset.sum_filter, Finset.sum_product]
  rw [hex, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hset : (Finset.range (k + 1)).filter (fun l => 2 * l < j) =
      insert 0 ((Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    have := Finset.mem_Icc.mp hj
    omega
  rw [hset, Finset.sum_insert (by simp)]
  simp only [Nat.mul_zero, Nat.sub_zero, pow_zero, mul_one]
  change tj n d k T j + _ ≤ _
  have ht := tj_nonneg_local (d := d) k T j
  let G : ℕ → ℝ := fun l => ((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * 4 ^ l *
    (cQ j l : ℝ) ^ 2 / ((j.factorial : ℝ) * j * (n : ℝ) ^ l)
  have hh : (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j),
      ((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * 4 ^ l * aSq n d T j l /
        (n : ℝ) ^ (k - (j - 2 * l))) ≤
      (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j), G l) * tj n d k T j := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro l hl
    exact weighted_trace_le_local hn k T j l hj (by have := (Finset.mem_filter.mp hl).2; omega)
      _ (by positivity)
  have hm : 1 + (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j), G l) ≤ rhoBar n k :=
    by
      exact le_maxJ_local k (fun j => 1 + ∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j),
        ((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * 4 ^ l * (cQ j l : ℝ) ^ 2 /
          ((j.factorial : ℝ) * j * (n : ℝ) ^ l)) j hj
  calc
    _ ≤ tj n d k T j + (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j), G l) * tj n d k T j :=
      add_le_add le_rfl hh
    _ = (1 + (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j), G l)) * tj n d k T j := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hm ht

private lemma bEff_decompose_local (k : ℕ) (T : Tens n) (s : ℕ) (hs : s ∈ Finset.Icc 1 k)
    (hν0 : nuC n d s 0 = 1) (w : Fin s → Fin n) :
    aT n d T s 0 w = bEff n d k T s w - ∑ l ∈ Finset.Icc 1 (Ls k s),
      nuC n d s l * aT n d T (s + 2 * l) l (fun t => w ⟨t.val, by have := t.isLt; omega⟩) := by
  classical
  have hset : (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k) =
      insert 0 (Finset.Icc 1 (Ls k s)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_Icc, Ls]
    have := Finset.mem_Icc.mp hs
    omega
  unfold bEff
  rw [hset, Finset.sum_insert (by simp), hν0]
  simp only [Nat.mul_zero, Nat.add_zero, one_mul]
  rw [add_sub_cancel_right]
  congr 1

private lemma cascade_level_local (hn : 1 ≤ n) (k : ℕ) (T : Tens n) (η : ℝ) (hη : 0 < η)
    (s : ℕ) (hs : s ∈ Finset.Icc 1 k) (hν0 : nuC n d s 0 = 1)
    (hν : ∀ l ∈ Finset.Icc 1 (Ls k s), 0 ≤ nuC n d s l ∧ nuC n d s l ≤ ((d : ℝ) + 1) ^ l) :
    tj n d k T s ≤ (1 + η) * ((s.factorial : ℝ) * s * frob (bEff n d k T s) / (n : ℝ) ^ (k - s)) +
      (1 + 1 / η) * ∑ l ∈ Finset.Icc 1 (Ls k s),
        (Ls k s : ℝ) * ((s.factorial : ℝ) * s * ((d : ℝ) + 1) ^ (2 * l) *
          (cQ (s + 2 * l) l : ℝ) ^ 2 / (((s + 2 * l).factorial : ℝ) * (s + 2 * l))) /
          (n : ℝ) ^ l * tj n d k T (s + 2 * l) := by
  classical
  let C : ℕ → (Fin s → Fin n) → ℝ := fun l w => nuC n d s l *
    aT n d T (s + 2 * l) l (fun t => w ⟨t.val, by have := t.isLt; omega⟩)
  have hC (l : ℕ) : frob (C l) = nuC n d s l ^ 2 * aSq n d T (s + 2 * l) l := by
    unfold C frob
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    rw [← aT_frob_local, ← frob_cast_local s l]
    rfl
  have hCs (l : ℕ) (hl : l ∈ Finset.Icc 1 (Ls k s)) :
      frob (C l) ≤ ((d : ℝ) + 1) ^ (2 * l) * aSq n d T (s + 2 * l) l := by
    rw [hC]
    have hp := pow_le_pow_left₀ (hν l hl).1 (hν l hl).2 2
    rw [← pow_mul, Nat.mul_comm l 2] at hp
    apply mul_le_mul_of_nonneg_right hp
    unfold aSq frob
    have hD : 0 ≤ DD n d := by unfold DD; positivity
    positivity
  have hA := frob_sum_error_local η hη (Finset.Icc 1 (Ls k s))
    (aT n d T s 0) (bEff n d k T s) C (bEff_decompose_local k T s hs hν0)
  rw [aT_frob_local, Nat.card_Icc] at hA
  simp only [Nat.add_sub_cancel] at hA
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let W : ℝ := (s.factorial : ℝ) * s / (n : ℝ) ^ (k - s)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have h := mul_le_mul_of_nonneg_left hA hW
  have ht : W * aSq n d T s 0 = tj n d k T s := by dsimp [W, tj]; ring
  rw [ht] at h
  refine h.trans ?_
  have hsum : W * ∑ l ∈ Finset.Icc 1 (Ls k s), frob (C l) ≤
      ∑ l ∈ Finset.Icc 1 (Ls k s),
        ((s.factorial : ℝ) * s * ((d : ℝ) + 1) ^ (2 * l) * (cQ (s + 2 * l) l : ℝ) ^ 2 /
          (((s + 2 * l).factorial : ℝ) * (s + 2 * l) * (n : ℝ) ^ l)) * tj n d k T (s + 2 * l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    have hj : s + 2 * l ∈ Finset.Icc 1 k := by
      simp only [Finset.mem_Icc, Ls] at *
      omega
    have htr := weighted_trace_le_local (d := d) hn k T (s + 2 * l) l hj (by omega)
      ((s.factorial : ℝ) * s * ((d : ℝ) + 1) ^ (2 * l)) (by positivity)
    simp only [Nat.add_sub_cancel_right] at htr
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at htr
    have hh := mul_le_mul_of_nonneg_left (hCs l hl) hW
    refine hh.trans ?_
    convert htr using 1 <;> (try dsimp [W]) <;> ring
  have hh := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ (1 + 1 / η) * (Ls k s : ℝ))
  have he : W * ((1 + η) * frob (bEff n d k T s) +
      (1 + 1 / η) * (Ls k s : ℝ) * ∑ l ∈ Finset.Icc 1 (Ls k s), frob (C l)) =
      (1 + η) * ((s.factorial : ℝ) * s * frob (bEff n d k T s) / (n : ℝ) ^ (k - s)) +
      ((1 + 1 / η) * (Ls k s : ℝ)) * (W * ∑ l ∈ Finset.Icc 1 (Ls k s), frob (C l)) := by
    dsimp [W]; ring
  rw [he]
  refine (add_le_add le_rfl hh).trans_eq ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  field_simp
  <;> ring

/-- **The cascade** (Lemma `LF` (ii), first part): `Σ_j t_j ≤ (1+η)/(1 − (1+1/η)θ̃) · Σ_s β_s` and
`𝒩(f) ≤ K_c Σ_s β_s`, with `β_s = n^{−(k−s)} s! s ‖b_s‖²`. -/
theorem cascade (hn : 1 ≤ n) (k : ℕ) (T : Tens n) (η : ℝ) (hη : 0 < η)
    (hθ : (1 + 1 / η) * thetaT n d k < 1)
    (hν0 : ∀ s ∈ Finset.Icc 1 k, nuC n d s 0 = 1)
    (hν : ∀ s ∈ Finset.Icc 1 k, ∀ l, 1 ≤ l → s + 2 * l ≤ k → 0 ≤ nuC n d s l ∧ nuC n d s l ≤ ((d : ℝ) + 1) ^ l) :
    ∑ j ∈ Finset.Icc 1 k, tj n d k T j ≤ (1 + η) / (1 - (1 + 1 / η) * thetaT n d k) *
      ∑ s ∈ Finset.Icc 1 k, (s.factorial : ℝ) * s * frob (bEff n d k T s) / (n : ℝ) ^ (k - s) ∧
    Nn n d k T ≤ Kc n d k η *
      ∑ s ∈ Finset.Icc 1 k, (s.factorial : ℝ) * s * frob (bEff n d k T s) / (n : ℝ) ^ (k - s) := by
  classical
  let B : ℝ := ∑ s ∈ Finset.Icc 1 k,
    (s.factorial : ℝ) * s * frob (bEff n d k T s) / (n : ℝ) ^ (k - s)
  let V : ℝ := ∑ j ∈ Finset.Icc 1 k, tj n d k T j
  let E : ℕ → ℕ → ℝ := fun s l => (Ls k s : ℝ) *
    ((s.factorial : ℝ) * s * ((d : ℝ) + 1) ^ (2 * l) * (cQ (s + 2 * l) l : ℝ) ^ 2 /
      (((s + 2 * l).factorial : ℝ) * (s + 2 * l))) / (n : ℝ) ^ l * tj n d k T (s + 2 * l)
  have hlevel (s : ℕ) (hs : s ∈ Finset.Icc 1 k) : tj n d k T s ≤
      (1 + η) * ((s.factorial : ℝ) * s * frob (bEff n d k T s) / (n : ℝ) ^ (k - s)) +
        (1 + 1 / η) * ∑ l ∈ Finset.Icc 1 (Ls k s), E s l := by
    apply cascade_level_local hn k T η hη s hs (hν0 s hs)
    intro l hl
    have hl' := Finset.mem_Icc.mp hl
    exact hν s hs l hl'.1 (by dsimp [Ls] at hl'; have := Finset.mem_Icc.mp hs; omega)
  have herror : (∑ s ∈ Finset.Icc 1 k, ∑ l ∈ Finset.Icc 1 (Ls k s), E s l) ≤ thetaT n d k * V := by
    rw [cascade_reindex_local]
    dsimp [V]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have he : (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j), E (j - 2 * l) l) =
        (∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j), (Ls k (j - 2 * l) : ℝ) *
          (((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * ((d : ℝ) + 1) ^ (2 * l) *
            (cQ j l : ℝ) ^ 2 / ((j.factorial : ℝ) * j)) / (n : ℝ) ^ l) * tj n d k T j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      have hl' := (Finset.mem_filter.mp hl).2
      dsimp [E]
      rw [Nat.sub_add_cancel (by omega : 2 * l ≤ j)]
      have hecast : (j - 2 * l : ℕ) + (2 : ℝ) * l = (j : ℝ) := by
        exact_mod_cast (Nat.sub_add_cancel (by omega : 2 * l ≤ j))
      rw [hecast]
    rw [he]
    apply mul_le_mul_of_nonneg_right _ (tj_nonneg_local k T j)
    unfold thetaT
    exact le_maxJ_local k (fun j => ∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j),
      (Ls k (j - 2 * l) : ℝ) * (((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) *
        ((d : ℝ) + 1) ^ (2 * l) * (cQ j l : ℝ) ^ 2 / ((j.factorial : ℝ) * j)) / (n : ℝ) ^ l) j hj
  have hv : V ≤ (1 + η) * B + (1 + 1 / η) * thetaT n d k * V := by
    have hh := Finset.sum_le_sum (s := Finset.Icc 1 k) hlevel
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hh
    refine hh.trans ?_
    dsimp [B]
    apply add_le_add le_rfl
    convert mul_le_mul_of_nonneg_left herror (by positivity : 0 ≤ 1 + 1 / η) using 1
    ring
  have hden : 0 < 1 - (1 + 1 / η) * thetaT n d k := by linarith
  have hmain : V ≤ (1 + η) / (1 - (1 + 1 / η) * thetaT n d k) * B := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hv]
  refine ⟨hmain, ?_⟩
  have hnorm := Nn_trace_bound_local (d := d) hn k T
  have hr : 0 ≤ rhoBar n k := maxJ_nonneg_local k _
  have hh := mul_le_mul_of_nonneg_left hmain hr
  refine hnorm.trans (hh.trans_eq ?_)
  unfold Kc
  dsimp [B]
  ring

/-- **Lemma `LF` (ii), second part**: `E P_α ≥ μ_n Σ_s n^{−(k−s)} s! s ‖b_s‖²`, and `P_α` is integrable. -/
theorem EP_lower (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hkd : k * d ≤ n) (T : Tens n)
    (hT : TSymm k T) :
    Integrable (Palpha k T) (stdGauss (CoefIdxD n d)) ∧
    muN n d k * ∑ s ∈ Finset.Icc 1 k, (s.factorial : ℝ) * s * frob (bEff n d k T s) / (n : ℝ) ^ (k - s) ≤
      ∫ Z, Palpha k T Z ∂stdGauss (CoefIdxD n d) := by
  classical
  let C : ℕ → (CoefIdxD n d → ℝ) → ℝ := fun s Z =>
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d), qS (bEff n d k T s) S Z ^ 2
  have hC (s : ℕ) (hs : s ∈ Finset.Icc 1 k) :=
    LC_mean hn hd s (Finset.mem_Icc.mp hs).1 (bEff n d k T s) (bEff_symm k T hT s)
  have hInt : Integrable (Palpha k T) (stdGauss (CoefIdxD n d)) := by
    unfold Palpha
    exact integrable_finsetSum _ (fun s hs => (qSquares_integrable (bEff n d k T s)).div_const _)
  refine ⟨hInt, ?_⟩
  have hE : (∫ Z, Palpha k T Z ∂stdGauss (CoefIdxD n d)) =
      ∑ s ∈ Finset.Icc 1 k, (lamS n d s * (s.factorial : ℝ) * frob (bEff n d k T s) /
        (d.factorial : ℝ) ^ s) / (n : ℝ) ^ (k - s) := by
    unfold Palpha
    rw [integral_finsetSum _ (fun s hs => (qSquares_integrable (bEff n d k T s)).div_const _)]
    apply Finset.sum_congr rfl
    intro s hs
    rw [integral_div, (hC s hs).2]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfac : (1 : ℝ) ≤ d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hratio (i : ℕ) (hi : i < k * d) :
      0 ≤ ((n : ℝ) - i) / ((n : ℝ) + 2 * i) ∧
        ((n : ℝ) - i) / ((n : ℝ) + 2 * i) ≤ 1 := by
    have hi' : (i : ℝ) ≤ n := by exact_mod_cast (show i ≤ n by omega)
    have hden : 0 < (n : ℝ) + 2 * i := by positivity
    refine ⟨div_nonneg (sub_nonneg.mpr hi') hden.le, (div_le_one hden).mpr ?_⟩
    have : (0 : ℝ) ≤ i := by positivity
    linarith
  have hl0 : 0 ≤ lamS n d k := Finset.prod_nonneg (fun i hi => (hratio i (Finset.mem_range.mp hi)).1)
  rw [hE, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  obtain ⟨hs1, hsk⟩ := Finset.mem_Icc.mp hs
  have hsd : s * d ≤ k * d := Nat.mul_le_mul_right d hsk
  have hls0 : 0 ≤ lamS n d s := Finset.prod_nonneg
    (fun i hi => (hratio i (lt_of_lt_of_le (Finset.mem_range.mp hi) hsd)).1)
  have hl : lamS n d k ≤ lamS n d s := by
    unfold lamS
    rw [← Finset.prod_range_mul_prod_Ico _ hsd]
    apply mul_le_of_le_one_right hls0
    apply Finset.prod_le_one₀
    · intro i hi
      exact (hratio i (Finset.mem_Ico.mp hi).2).1
    · intro i hi
      exact (hratio i (Finset.mem_Ico.mp hi).2).2
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hpow : (d.factorial : ℝ) ^ s ≤ (d.factorial : ℝ) ^ k := pow_le_pow_right₀ hfac hsk
  have hden : (s : ℝ) * (d.factorial : ℝ) ^ s ≤ (k : ℝ) * (d.factorial : ℝ) ^ k :=
    mul_le_mul (by exact_mod_cast hsk) hpow (by positivity) (by positivity)
  have hmu : muN n d k ≤ lamS n d s / (s * (d.factorial : ℝ) ^ s) := by
    exact div_le_div₀ hls0 hl (by positivity) hden
  have hms : muN n d k * s ≤ lamS n d s / (d.factorial : ℝ) ^ s := by
    have hh := mul_le_mul_of_nonneg_right hmu hs0.le
    convert hh using 1
    field_simp
  have hb0 : 0 ≤ (s.factorial : ℝ) * frob (bEff n d k T s) := by
    unfold frob
    positivity
  have hh := mul_le_mul_of_nonneg_right hms hb0
  rw [← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < (n : ℝ) ^ (k - s))).mpr
  convert hh using 1 <;> ring

end BstLean.Part41

