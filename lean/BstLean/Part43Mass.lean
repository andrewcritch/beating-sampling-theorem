import BstLean.Part43Defs

/-!
# Part 43, wave 1: the mass bound for every sign-symmetric law (Lemma M)

Paper: `proofs/option-m/43-arbitrary-degree-every-diagonal-bingham.tex`. Specification:
`delegations/answers/p43-spec-opus.md`. Replace each `sorry` by a proof. Do not edit the statements.
Do not use `native_decide` or `axiom` anywhere.

Suggested route.
* `HR_symm`: the product `∏ t, phiM x (w t)` is invariant under permutations of `w`.
* `HR_nonneg`: `∏ φ_{w_t} = x^e`; if some `e_a` is odd, the flip `flipAt a` changes the sign of the
  integrand and fixes `μ`, so `HR = 0`; otherwise the integrand is `≥ 0`.
* `mass43`: `Σ_w H_{j,l}[w] = Σ_{c,w} G_j[(c,c,w)]` (distinct entries of `G_j`, all `≥ 0`) `≤ S_j`.
  `S_j = Σ_β N_j(2β) E u^β ≤ sup_{u ∈ Δ} Σ_β N_j(2β) u^β`, and for each `m`
  `Σ_{|β|=m} N_j(2β) u^β ≤ max_β (N_j(2β) β!/m!) (Σ u)^m`. `N_j(2β)` depends only on the multiset of
  nonzero entries of `β`, so the maximum over `β ∈ ℕⁿ` equals the maximum over `β : Fin m → ℕ`.
* `Upp_one`: the `m = 0` term is `Nj j d 0 _ = 1`; the other terms are `≥ 0`.
-/

namespace BstLean.Part43

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD rhoD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT mset wordOf Tens TSymm fval varU sdU
  levels cQ kapQ muQ aT Nn uJ Pcal r2 rhoZ cS Bfix Pn epsS baseline thetaT rhoBar Kc GamP etaR etaK Lk
  orbSize heavyCount bQ In41)
open BstLean.Part40 (SphLaw SignSym)

variable {n d : ℕ}

theorem HR_symm (μ : Measure (Fin n → ℝ)) {s : ℕ} (l : ℕ) :
    IsSymmT (fun w : Fin s → Mono n d => HR μ l w) := by
  classical
  intro σ w
  unfold HR
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  exact Equiv.prod_comp σ (fun t => phiM x (w t))

private lemma mono_powers (x : Fin n → ℝ) (u : Multiset (Fin n)) :
    BstLean.Part36.monoVal x u = ∏ a, x a ^ u.count a := by
  classical
  induction u using Multiset.induction_on with
  | empty => simp [BstLean.Part36.monoVal]
  | @cons a u ih =>
    simp only [BstLean.Part36.monoVal, Multiset.map_cons, Multiset.prod_cons] at *
    rw [ih]
    simp only [Multiset.count_cons]
    have he (b : Fin n) : x b ^ (u.count b + (if b = a then 1 else 0)) =
        (if b = a then x a else 1) * x b ^ u.count b := by
      split_ifs with h
      · subst b; rw [pow_add, pow_one]; ring
      · simp
    simp_rw [he, Finset.prod_mul_distrib]
    simp

private lemma word_powers {s : ℕ} (x : Fin n → ℝ) (w : Fin s → Mono n d) :
    (∏ t, phiM x (w t)) = ∏ a, x a ^ (∑ t, (w t).2.1.count a) := by
  classical
  simp_rw [phiM, mono_powers]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro a _
  exact Finset.prod_pow_eq_pow_sum Finset.univ (fun t => (w t).2.1.count a) (x a)

private lemma phiSq_flip (i : Fin n) (x : Fin n → ℝ) :
    phiSq d (BstLean.Part40.flipAt i x) = phiSq d x := by
  classical
  unfold phiSq
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [phiM, mono_powers, ← Finset.prod_pow, ← pow_mul,
    mul_comm _ 2, pow_mul]
  congr 1
  ext a
  by_cases h : a = i <;> simp [BstLean.Part40.flipAt, h]

theorem HR_nonneg {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ) {s : ℕ} (l : ℕ) (w : Fin s → Mono n d) :
    0 ≤ HR μ l w := by
  classical
  let e : Fin n → ℕ := fun a => ∑ t, (w t).2.1.count a
  by_cases he : ∀ a, Even (e a)
  · apply integral_nonneg
    intro x
    change 0 ≤ phiSq d x ^ l * ∏ t, phiM x (w t)
    rw [word_powers]
    apply mul_nonneg
    · exact pow_nonneg (Finset.sum_nonneg fun p _ => sq_nonneg _) _
    · exact Finset.prod_nonneg fun a _ => (he a).pow_nonneg _
  · obtain ⟨i, hi⟩ := not_forall.mp he
    have ho : Odd (e i) := Nat.not_even_iff_odd.mp hi
    let f : (Fin n → ℝ) → ℝ := fun x => phiSq d x ^ l * ∏ t, phiM x (w t)
    have hf : Continuous f := by
      dsimp [f, phiSq, phiM, BstLean.Part36.monoVal]
      fun_prop
    have hm : Measurable (BstLean.Part40.flipAt i) := by
      apply Measurable.of_eval
      intro a
      dsimp [BstLean.Part40.flipAt]
      split_ifs <;> fun_prop
    have hflip (x : Fin n → ℝ) : f (BstLean.Part40.flipAt i x) = -f x := by
      dsimp [f]
      rw [phiSq_flip, word_powers, word_powers]
      change phiSq d x ^ l * (∏ a, BstLean.Part40.flipAt i x a ^ e a) =
        -(phiSq d x ^ l * ∏ a, x a ^ e a)
      rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
        (fun a => BstLean.Part40.flipAt i x a ^ e a),
        Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
        (fun a => x a ^ e a)]
      have hr : (∏ a ∈ Finset.univ \ {i}, BstLean.Part40.flipAt i x a ^ e a) =
          ∏ a ∈ Finset.univ \ {i}, x a ^ e a := by
        apply Finset.prod_congr rfl
        intro a ha
        have hai : a ≠ i := by simpa using (Finset.mem_sdiff.mp ha).2
        simp [BstLean.Part40.flipAt, hai]
      rw [hr]
      simp [BstLean.Part40.flipAt, ho.neg_pow]
    have hv : (∫ x, f (BstLean.Part40.flipAt i x) ∂μ) = ∫ x, f x ∂μ := by
      rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable, hμ.flip i]
    simp_rw [hflip, integral_neg] at hv
    change 0 ≤ ∫ x, f x ∂μ
    linarith

private lemma sphere_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable f μ := by
  let := hμ.prob
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hμ.sphere] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma traced_mass_le_raw {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ)
    (j l : ℕ) (hjl : 2 * l ≤ j) :
    massR μ d j l ≤ ∑ v : Fin j → Mono n d, HR μ 0 v := by
  classical
  let α := (Fin l ⊕ Fin l) ⊕ Fin (j - 2 * l)
  let e : α ≃ Fin j := Fintype.equivOfCardEq (by simp [α]; omega)
  let pack : ((Fin (j - 2 * l) → Mono n d) × (Fin l → Mono n d)) →
      (Fin j → Mono n d) :=
    fun p i => Sum.elim (Sum.elim p.2 p.2) p.1 (e.symm i)
  have hinj : Function.Injective pack := by
    intro p q hpq
    apply Prod.ext
    · funext t
      simpa [pack] using congrFun hpq (e (Sum.inr t))
    · funext t
      simpa [pack] using congrFun hpq (e (Sum.inl (Sum.inl t)))
  have hp (p : (Fin (j - 2 * l) → Mono n d) × (Fin l → Mono n d))
      (x : Fin n → ℝ) :
      (∏ t, phiM x (pack p t)) = (∏ t, phiM x (p.2 t) ^ 2) * ∏ t, phiM x (p.1 t) := by
    have ht := (e.prod_comp (fun i => phiM x (pack p i))).symm
    dsimp [α] at ht
    simp only [pack, Equiv.symm_apply_apply, Fintype.prod_sum_type, Sum.elim_inl,
      Sum.elim_inr] at ht
    rw [ht, Finset.prod_pow, pow_two]
  have hH (w : Fin (j - 2 * l) → Mono n d) : HR μ l w =
      ∑ c : Fin l → Mono n d, HR μ 0 (pack (w, c)) := by
    unfold HR
    simp only [pow_zero, one_mul]
    rw [← integral_finsetSum]
    · apply integral_congr_ae
      filter_upwards [] with x
      simp_rw [hp]
      rw [← Finset.sum_mul, ← Fintype.prod_sum
        (fun (_ : Fin l) (p : Mono n d) => phiM x p ^ 2)]
      simp [phiSq]
    · intro c _
      apply sphere_integrable hμ.sph
      dsimp [phiM, BstLean.Part36.monoVal]
      fun_prop
  unfold massR
  simp_rw [abs_of_nonneg (HR_nonneg hμ _ _), hH]
  rw [← Fintype.sum_prod_type
    (fun p : (Fin (j - 2 * l) → Mono n d) × (Fin l → Mono n d) => HR μ 0 (pack p))]
  calc
    _ = ∑ v ∈ Finset.univ.image pack, HR μ 0 v := by
      rw [Finset.sum_image]
      exact fun p _ q _ hpq => hinj hpq
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ => HR_nonneg hμ 0 v)

private lemma simplex_coefficient_bound (m : ℕ) (u : Fin n → ℝ)
    (hu : ∀ a, 0 ≤ u a) (C : (Fin n → ℕ) → ℝ) (U : ℝ)
    (hC : ∀ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) m,
      C β ≤ U * (Nat.multinomial Finset.univ β : ℝ)) :
    (∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) m,
      C β * ∏ a, u a ^ β a) ≤ U * (∑ a, u a) ^ m := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro β hβ
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hC β hβ)
    (Finset.prod_nonneg fun a _ => pow_nonneg (hu a) _)

private lemma ratio_le_UppTerm (j d m : ℕ) (β : Fin m → ℕ) (hβ : ∑ a, β a = m) :
    (Nj j d m β : ℝ) * (∏ a, (β a).factorial : ℝ) / (m.factorial : ℝ) ≤
      UppTerm j d m := by
  classical
  have hb (a : Fin m) : β a < m + 1 := by
    have h := Finset.single_le_sum (fun b _ => Nat.zero_le (β b)) (Finset.mem_univ a)
    rw [hβ] at h
    omega
  let βf : Fin m → Fin (m + 1) := fun a => ⟨β a, hb a⟩
  unfold UppTerm
  apply List.le_max_of_le' 0
  · apply List.mem_map.mpr
    refine ⟨βf, ?_, rfl⟩
    rw [Finset.mem_toList, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hβ⟩
  · rfl

private lemma sum_extend {α γ : Type*} [Fintype α] [Fintype γ]
    (f : α ↪ γ) (b : α → ℕ) :
    (∑ i, Function.extend f b 0 i) = ∑ i, b i := by
  classical
  symm
  apply Fintype.sum_of_injective f f.injective
  · intro i hi
    exact Function.extend_apply' _ _ _ hi
  · intro i
    exact (f.injective.extend_apply _ _ _).symm

private lemma prod_factorial_extend {α γ : Type*} [Fintype α] [Fintype γ]
    (f : α ↪ γ) (b : α → ℕ) :
    (∏ i, (Function.extend f b 0 i).factorial) = ∏ i, (b i).factorial := by
  classical
  symm
  apply Fintype.prod_of_injective f f.injective
  · intro i hi
    rw [Function.extend_apply' _ _ _ hi]
    rfl
  · intro i
    rw [f.injective.extend_apply]

private lemma Nj_ratio_bound (j d m : ℕ) (β : Fin n → ℕ) (hβ : ∑ a, β a = m) :
    (Nj j d n β : ℝ) * (∏ a, (β a).factorial : ℝ) / (m.factorial : ℝ) ≤
      UppTerm j d m := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun a => β a ≠ 0)
  have hzero (a : Fin n) (ha : a ∉ A) : β a = 0 := by
    simpa [A] using ha
  have hsum : (∑ a : A, β a) = m := by
    rw [Finset.sum_coe_sort]
    calc
      (∑ a ∈ A, β a) = ∑ a, β a := Finset.sum_subset (Finset.subset_univ _)
        (fun a _ ha => hzero a ha)
      _ = m := hβ
  have hcard : Fintype.card A ≤ Fintype.card (Fin m) := by
    rw [Fintype.card_fin, ← hsum]
    calc
      Fintype.card A = ∑ _a : A, 1 := by simp
      _ ≤ ∑ a : A, β a := by
        apply Finset.sum_le_sum
        intro a _
        have ha : β a ≠ 0 := (Finset.mem_filter.mp a.property).2
        omega
  let f : A ↪ Fin m := Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  let βc : Fin m → ℕ := Function.extend f (fun a : A => β a) 0
  have hβc : (∑ a, βc a) = m := (sum_extend f _).trans hsum
  have hprod : (∏ a, (βc a).factorial) = ∏ a, (β a).factorial := by
    rw [prod_factorial_extend f, Finset.prod_coe_sort A (fun a => (β a).factorial)]
    exact Finset.prod_subset (Finset.subset_univ _) (fun a _ ha => by rw [hzero a ha]; rfl)
  let S : Finset (Fin j → Fin n → Fin (d + 1)) := Finset.univ.filter fun e =>
    (∀ t, ∑ a, (e t a : ℕ) ≤ d) ∧ (∀ a, ∑ t, (e t a : ℕ) = 2 * β a)
  let C (e : Fin j → Fin n → Fin (d + 1)) : Fin j → Fin m → Fin (d + 1) :=
    fun t => Function.extend f (fun a : A => e t a) 0
  have hezero (e) (he : e ∈ S) (a : Fin n) (ha : a ∉ A) (t : Fin j) : e t a = 0 := by
    have hc := (Finset.mem_filter.mp he).2.2 a
    rw [hzero a ha, mul_zero] at hc
    have ht := Finset.single_le_sum (fun t _ => Nat.zero_le (e t a : ℕ)) (Finset.mem_univ t)
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  have hCmem (e) (he : e ∈ S) :
      C e ∈ (Finset.univ : Finset (Fin j → Fin m → Fin (d + 1))).filter (fun e =>
        (∀ t, ∑ a, (e t a : ℕ) ≤ d) ∧ (∀ a, ∑ t, (e t a : ℕ) = 2 * βc a)) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro t
      have hs : (∑ a, (C e t a : ℕ)) = ∑ a : A, (e t a : ℕ) := by
        symm
        apply Fintype.sum_of_injective f f.injective
        · intro a ha
          simp [C, Function.extend_apply' _ _ _ ha]
        · intro a
          simp [C, f.injective.extend_apply]
      rw [hs, Finset.sum_coe_sort A (fun a => (e t a : ℕ))]
      exact (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans
        ((Finset.mem_filter.mp he).2.1 t)
    · intro a
      by_cases ha : a ∈ Set.range f
      · obtain ⟨b, rfl⟩ := ha
        simpa [C, βc, f.injective.extend_apply] using (Finset.mem_filter.mp he).2.2 b
      · simp [C, βc, Function.extend_apply' _ _ _ ha]
  have hCinj : Set.InjOn C S := by
    intro e he e' he' hh
    funext t a
    by_cases ha : a ∈ A
    · let b : A := ⟨a, ha⟩
      have h := congrFun (congrFun hh t) (f b)
      simpa [C, f.injective.extend_apply, b] using h
    · rw [hezero e he a ha t, hezero e' he' a ha t]
  have hNj : Nj j d n β ≤ Nj j d m βc := by
    exact Finset.card_le_card_of_injOn C hCmem hCinj
  have hratio := ratio_le_UppTerm j d m βc hβc
  rw [← Nat.cast_prod, hprod, Nat.cast_prod] at hratio
  apply le_trans _ hratio
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast hNj) (by positivity)

private lemma Nj_coefficient_bound (j d m : ℕ) (β : Fin n → ℕ) (hβ : ∑ a, β a = m) :
    (Nj j d n β : ℝ) ≤ UppTerm j d m * (Nat.multinomial Finset.univ β : ℝ) := by
  classical
  have h := Nj_ratio_bound j d m β hβ
  have hP : 0 < (∏ a, ((β a).factorial : ℝ)) := Finset.prod_pos fun a _ => by positivity
  have hF : 0 < (m.factorial : ℝ) := by positivity
  have hc : (∏ a, ((β a).factorial : ℝ)) * (Nat.multinomial Finset.univ β : ℝ) =
      (m.factorial : ℝ) := by
    exact_mod_cast (Nat.multinomial_spec Finset.univ β).trans (congrArg Nat.factorial hβ)
  apply (mul_le_mul_iff_left₀ hP).mp
  calc
    _ ≤ UppTerm j d m * (m.factorial : ℝ) := (div_le_iff₀ hF).mp h
    _ = _ := by rw [← hc]; ring

private lemma even_half (a : ℕ) (ha : Even a) : 2 * (a / 2) = a := by
  obtain ⟨b, rfl⟩ := ha
  omega

private lemma matrix_simplex_bound (j d : ℕ) (u : Fin n → ℝ)
    (hu : ∀ a, 0 ≤ u a) (hs : ∑ a, u a = 1) :
    (∑ e ∈ (Finset.univ : Finset (Fin j → Fin n → Fin (d + 1))).filter (fun e =>
        (∀ t, ∑ a, (e t a : ℕ) ≤ d) ∧ (∀ a, Even (∑ t, (e t a : ℕ)))),
      ∏ a, u a ^ ((∑ t, (e t a : ℕ)) / 2)) ≤ Upp j d := by
  classical
  let S : Finset (Fin j → Fin n → Fin (d + 1)) := Finset.univ.filter fun e =>
    (∀ t, ∑ a, (e t a : ℕ) ≤ d) ∧ (∀ a, Even (∑ t, (e t a : ℕ)))
  let b (e : Fin j → Fin n → Fin (d + 1)) (a : Fin n) : ℕ := (∑ t, (e t a : ℕ)) / 2
  let q (e : Fin j → Fin n → Fin (d + 1)) : ℕ := ∑ a, b e a
  have heven (e) (he : e ∈ S) (a) : 2 * b e a = ∑ t, (e t a : ℕ) :=
    even_half _ ((Finset.mem_filter.mp he).2.2 a)
  have hq (e) (he : e ∈ S) : q e ∈ Finset.range (j * d / 2 + 1) := by
    have hh : 2 * q e ≤ j * d := by
      calc
        2 * q e = ∑ a, ∑ t, (e t a : ℕ) := by
          simp only [q, Finset.mul_sum, heven e he]
        _ = ∑ t, ∑ a, (e t a : ℕ) := Finset.sum_comm
        _ ≤ ∑ _t : Fin j, d := Finset.sum_le_sum fun t _ => (Finset.mem_filter.mp he).2.1 t
        _ = j * d := by simp
    simp only [Finset.mem_range]
    omega
  change (∑ e ∈ S, ∏ a, u a ^ b e a) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hq (fun e => ∏ a, u a ^ b e a)]
  unfold Upp
  apply Finset.sum_le_sum
  intro m hm
  let Sm := S.filter (fun e => q e = m)
  have hb (e) (he : e ∈ Sm) : b e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) m := by
    exact Finset.mem_piAntidiag.mpr ⟨(Finset.mem_filter.mp he).2, fun a _ => Finset.mem_univ a⟩
  have hfiber (β : Fin n → ℕ) (hβ : β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) m) :
      Sm.filter (fun e => b e = β) = Finset.univ.filter (fun e : Fin j → Fin n → Fin (d + 1) =>
        (∀ t, ∑ a, (e t a : ℕ) ≤ d) ∧ (∀ a, ∑ t, (e t a : ℕ) = 2 * β a)) := by
    ext e
    simp only [Sm, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨he, hq'⟩, hbe⟩
      have heS : e ∈ S := he
      refine ⟨(Finset.mem_filter.mp heS).2.1, ?_⟩
      intro a
      rw [← heven e heS a, hbe]
    · rintro ⟨he, hcol⟩
      have hbe : b e = β := by
        funext a
        dsimp [b]
        rw [hcol a]
        omega
      refine ⟨⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, ?_⟩, ?_⟩, hbe⟩
      · intro a
        rw [hcol a]
        exact even_two_mul _
      · change (∑ a, b e a) = m
        rw [hbe]
        exact (Finset.mem_piAntidiag.mp hβ).1
  have heq : (∑ e ∈ Sm, ∏ a, u a ^ b e a) =
      ∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) m,
        (Nj j d n β : ℝ) * ∏ a, u a ^ β a := by
    rw [← Finset.sum_fiberwise_of_maps_to' hb (fun β => ∏ a, u a ^ β a)]
    apply Finset.sum_congr rfl
    intro β hβ
    rw [hfiber β hβ, Finset.sum_const, nsmul_eq_mul]
    rfl
  change (∑ e ∈ Sm, ∏ a, u a ^ b e a) ≤ _
  rw [heq]
  have ht := simplex_coefficient_bound m u hu (fun β => (Nj j d n β : ℝ))
    (UppTerm j d m) (fun β hβ => Nj_coefficient_bound j d m β (Finset.mem_piAntidiag.mp hβ).1)
  simpa [hs] using ht

private lemma odd_power_integral {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ)
    (e : Fin n → ℕ) (i : Fin n) (ho : Odd (e i)) : (∫ x, ∏ a, x a ^ e a ∂μ) = 0 := by
  classical
  have hm : Measurable (BstLean.Part40.flipAt i) := by
    apply Measurable.of_eval
    intro a
    dsimp [BstLean.Part40.flipAt]
    split_ifs <;> fun_prop
  have hf : Continuous (fun x : Fin n → ℝ => ∏ a, x a ^ e a) := by fun_prop
  have hp (x : Fin n → ℝ) : (∏ a, BstLean.Part40.flipAt i x a ^ e a) = -(∏ a, x a ^ e a) := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun a => BstLean.Part40.flipAt i x a ^ e a),
      Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i) (fun a => x a ^ e a)]
    have hh : (∏ a ∈ Finset.univ \ {i}, BstLean.Part40.flipAt i x a ^ e a) =
        ∏ a ∈ Finset.univ \ {i}, x a ^ e a := by
      apply Finset.prod_congr rfl
      intro a ha
      have hai : a ≠ i := by simpa using (Finset.mem_sdiff.mp ha).2
      simp [BstLean.Part40.flipAt, hai]
    rw [hh]
    simp [BstLean.Part40.flipAt, ho.neg_pow]
  have hh : (∫ x, ∏ a, BstLean.Part40.flipAt i x a ^ e a ∂μ) = ∫ x, ∏ a, x a ^ e a ∂μ := by
    rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable, hμ.flip i]
  simp_rw [hp, integral_neg] at hh
  linarith

private lemma HR_zero_even {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ)
    {j : ℕ} (w : Fin j → Mono n d) :
    HR μ 0 w = ∫ x, if ∀ a, Even (∑ t, (w t).2.1.count a) then
      ∏ a, (x a ^ 2) ^ ((∑ t, (w t).2.1.count a) / 2) else 0 ∂μ := by
  classical
  unfold HR
  simp only [pow_zero, one_mul, word_powers]
  by_cases he : ∀ a, Even (∑ t, (w t).2.1.count a)
  · simp only [ite_eq_left he]
    apply integral_congr_ae
    filter_upwards [] with x
    apply Finset.prod_congr rfl
    intro a _
    rw [← pow_mul, even_half _ (he a)]
  · simp only [ite_eq_right he, integral_zero]
    obtain ⟨i, hi⟩ := not_forall.mp he
    exact odd_power_integral hμ _ i (Nat.not_even_iff_odd.mp hi)

private lemma mono_count_sum (p : Mono n d) : (∑ a, p.2.1.count a) = (p.1 : ℕ) := by
  rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
  exact p.2.property

private lemma mono_count_injective : Function.Injective (fun p : Mono n d => fun a => p.2.1.count a) := by
  intro p q h
  have he : p.2.1 = q.2.1 := Multiset.ext' (fun a => congrFun h a)
  have hi : p.1 = q.1 := Fin.ext (by
    have hc := congrArg Multiset.card he
    simpa only [p.2.property, q.2.property] using hc)
  cases p with
  | mk i p =>
    cases q with
    | mk i' q =>
      dsimp only at hi he
      subst i'
      congr 1
      exact Subtype.ext he

private lemma raw_mass_bound {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ) (j d : ℕ) :
    (∑ w : Fin j → Mono n d, HR μ 0 w) ≤ Upp j d := by
  classical
  let := hμ.sph.prob
  let b (w : Fin j → Mono n d) (a : Fin n) : ℕ := ∑ t, (w t).2.1.count a
  let E (w : Fin j → Mono n d) : Prop := ∀ a, Even (b w a)
  let P (w : Fin j → Mono n d) (x : Fin n → ℝ) : ℝ := ∏ a, (x a ^ 2) ^ (b w a / 2)
  let F (x : Fin n → ℝ) : ℝ := ∑ w : Fin j → Mono n d, if E w then P w x else 0
  have hcount (p : Mono n d) (a : Fin n) : p.2.1.count a < d + 1 := by
    have hc := Multiset.count_le_card a p.2.1
    rw [p.2.property] at hc
    exact hc.trans_lt p.1.isLt
  let C (w : Fin j → Mono n d) : Fin j → Fin n → Fin (d + 1) :=
    fun t a => ⟨(w t).2.1.count a, hcount (w t) a⟩
  have hCinj : Function.Injective C := by
    intro w v hwv
    funext t
    apply mono_count_injective
    funext a
    exact congrArg Fin.val (congrFun (congrFun hwv t) a)
  have hFC : Continuous F := by
    apply continuous_finsetSum
    intro w _
    by_cases he : E w
    · simp only [he, ite_true]
      dsimp [P]
      fun_prop
    · simp only [he, ite_false]
      fun_prop
  have hFeq : (∑ w : Fin j → Mono n d, HR μ 0 w) = ∫ x, F x ∂μ := by
    simp_rw [HR_zero_even hμ]
    rw [← integral_finsetSum]
    intro w _
    apply sphere_integrable hμ.sph
    change Continuous (fun x => if E w then P w x else 0)
    by_cases he : E w
    · simp only [he, ite_true]
      dsimp [P]
      fun_prop
    · simp only [he, ite_false]
      fun_prop
  rw [hFeq]
  calc
    (∫ x, F x ∂μ) ≤ ∫ _x, Upp j d ∂μ := by
      apply integral_mono_ae (sphere_integrable hμ.sph hFC) (integrable_const _)
      filter_upwards [hμ.sph.sphere] with x hx
      have hbound := matrix_simplex_bound j d (fun a => x a ^ 2) (fun a => sq_nonneg _) hx
      apply le_trans _ hbound
      dsimp [F]
      rw [← Finset.sum_filter]
      calc
        _ = ∑ e ∈ (Finset.univ.filter E).image C,
            ∏ a, (x a ^ 2) ^ ((∑ t, (e t a : ℕ)) / 2) := by
          rw [Finset.sum_image (fun w _ v _ h => hCinj h)]
        _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro e he
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, (Finset.mem_filter.mp hw).2⟩
            intro t
            change (∑ a, (w t).2.1.count a) ≤ d
            rw [mono_count_sum]
            have ht := (w t).1.isLt
            omega
          · intro e _ _
            exact Finset.prod_nonneg fun a _ => pow_nonneg (sq_nonneg _) _
    _ = Upp j d := by simp

/-- **Lemma M**: `S_{j,l}(μ) ≤ U″_j` for every sign-symmetric law on the sphere. -/
theorem mass43 (hd : 1 ≤ d) {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ) (j l : ℕ) (hjl : 2 * l < j) :
    massR μ d j l ≤ Upp j d := by
  exact (traced_mass_le_raw hμ j l (Nat.le_of_lt hjl)).trans (raw_mass_bound hμ j d)

private lemma UppTerm_nonneg (j d m : ℕ) : 0 ≤ UppTerm j d m := by
  unfold UppTerm
  generalize (((Finset.univ : Finset (Fin m → Fin (m + 1))).filter
    fun β => ∑ a, (β a : ℕ) = m).toList.map
    fun β => (Nj j d m (fun a => (β a : ℕ)) : ℝ) *
      (∏ a, ((β a : ℕ).factorial : ℝ)) / (m.factorial : ℝ)) = L
  induction L with
  | nil => simp
  | cons a L ih => exact le_max_of_le_right ih

theorem Upp_one (j d : ℕ) : 1 ≤ Upp j d := by
  classical
  have hz : UppTerm j d 0 = 1 := by
    simp [UppTerm, Nj]
  unfold Upp
  rw [← hz]
  exact Finset.single_le_sum (fun m _ => UppTerm_nonneg j d m) (by simp)

end BstLean.Part43
