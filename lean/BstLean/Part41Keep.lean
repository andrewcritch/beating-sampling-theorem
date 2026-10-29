import BstLean.Part41Defs

/-!
# Part 41, wave 1: the `ℓ¹` mass, the top-orbit tail, and the existence of the kept sets

Paper: Lemmas `mass` and `tail`, and the tail clause of Lemma `C`. Specification:
`delegations/answers/p41-spec-opus.md`. Do not use `native_decide`.

Routes. `mass_le`: the entries of `H_{j,l}` are sums of distinct entries of `G_j ≥ 0`, so
`S_{j,l} ≤ S_j`; then the paper's count: `S_j = 1 + Σ_s C(n,s) Σ_m g[s,m]/ρ_m(n)` by expanding
`∏_c (1 + G̃)` coordinate by coordinate, and `C(n,s)/ρ_m(n) ≤ n^{s−m}/s!` (`s ≤ m`). `tail_le`: keep the
`O` orbits with the largest common value (`max · sum` bound `v(S − T) ≤ T(S − T)/O ≤ S²/(4O)`).
`kept_exists`: `tail_le` at `O = Ocnt`, with `mass_le`, `HQ ≥ 0`, `HQ` symmetric, and the ceiling; if
`Ocnt` is the number of orbits, keep every orbit (`R = 0`).
-/

namespace BstLean.Part41

variable {n d : ℕ}

private lemma rhoQ_ge_pow (hn : 1 ≤ n) (m : ℕ) :
    (n : ℚ) ^ m ≤ rhoQ n m := by
  unfold rhoQ
  have heq : (n : ℚ) ^ m = ∏ _t ∈ Finset.range m, (n : ℚ) := by simp
  rw [heq]
  apply Finset.prod_le_prod₀
  · intro t _; positivity
  · intro t _; linarith [Nat.cast_nonneg (α := ℚ) t]

private lemma rhoQ_pos (hn : 1 ≤ n) (m : ℕ) : 0 < rhoQ n m := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  exact (pow_pos hnq m).trans_le (rhoQ_ge_pow hn m)

private lemma sphMomQ_nonneg (hn : 1 ≤ n) (e : Fin n → ℕ) :
    0 ≤ sphMomQ e := by
  unfold sphMomQ
  split_ifs
  · apply div_nonneg (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
    exact (rhoQ_pos hn _).le
  · rfl

private lemma sphMomQ_le (hn : 1 ≤ n) (e : Fin n → ℕ) :
    sphMomQ e ≤ if ∀ a, Even (e a) then
      (∏ a, ((e a - 1).doubleFactorial : ℚ)) / (n : ℚ) ^ ((∑ a, e a) / 2)
      else 0 := by
  unfold sphMomQ
  split_ifs
  · apply div_le_div_of_nonneg_left (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
      (by
        have hnq : (0 : ℚ) < n := by exact_mod_cast hn
        exact pow_pos hnq _)
      (rhoQ_ge_pow hn _)
  · rfl

private lemma choose_le_pow_div (hn : 1 ≤ n) (s : ℕ) :
    (n.choose s : ℚ) ≤ (n : ℚ) ^ s / (s.factorial : ℚ) := by
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < s.factorial)).mpr
  have h := Nat.descFactorial_le_pow n s
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm] at h
  exact_mod_cast h

private abbrev deg {j : ℕ} (e : Fin j →₀ ℕ) : ℕ := e.sum (fun _ b => b)

private lemma deg_eq_sum {j : ℕ} (e : Fin j →₀ ℕ) : deg e = ∑ i, e i := by
  exact Finsupp.sum_fintype _ _ (by simp)

private lemma deg_add {j : ℕ} (e f : Fin j →₀ ℕ) :
    deg (e + f) = deg e + deg f := by
  simp [deg_eq_sum, Finset.sum_add_distrib]

private lemma gt_support (j d : ℕ) (e : Fin j →₀ ℕ)
    (he : e ∈ (Gt j d).support) : 2 ≤ deg e ∧ Even (deg e) := by
  classical
  have he' := MvPolynomial.mem_support_iff.mp he
  unfold Gt at he'
  rw [MvPolynomial.coeff_sum] at he'
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero he'
  split_ifs at ha with hc
  · rw [MvPolynomial.coeff_monomial] at ha
    split_ifs at ha with heq
    · subst e
      have hdg : deg (Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))) =
          ∑ i, (a i : ℕ) := by simp [deg_eq_sum]
      rw [hdg]
      refine ⟨?_, hc.2⟩
      obtain ⟨r, hr⟩ := hc.2
      omega
    · exact (ha rfl).elim
  · exact (ha (by simp)).elim

private lemma gt_pow_support (j d s : ℕ) (e : Fin j →₀ ℕ)
    (he : e ∈ (Gt j d ^ s).support) : 2 * s ≤ deg e ∧ Even (deg e) := by
  classical
  induction s generalizing e with
  | zero =>
    have : e = 0 := by simpa using he
    subst e
    simp [deg]
  | succ s ih =>
    rw [pow_succ] at he
    have hm := MvPolynomial.support_mul (Gt j d ^ s) (Gt j d) he
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hm
    subst e
    obtain ⟨hda, hea⟩ := ih a ha
    obtain ⟨hdb, heb⟩ := gt_support j d b hb
    rw [deg_add]
    exact ⟨by omega, hea.add heb⟩

private lemma gt_coeff_nonneg (j d s : ℕ) (e : Fin j →₀ ℕ) :
    0 ≤ (Gt j d ^ s).coeff e := by
  classical
  induction s generalizing e with
  | zero => simp [MvPolynomial.coeff_one]; split_ifs <;> norm_num
  | succ s ih =>
    rw [pow_succ, MvPolynomial.coeff_mul]
    apply Finset.sum_nonneg
    intro p _
    apply mul_nonneg (ih p.1)
    unfold Gt
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · rw [MvPolynomial.coeff_monomial]
      split_ifs <;> positivity
    · simp

private def coeffMap (j : ℕ) :
    MvPolynomial (Fin j) ℚ →ₗ[ℚ] ((Fin j →₀ ℕ) →₀ ℚ) where
  toFun := AddMonoidAlgebra.coeff
  map_add' := by intros; simp
  map_smul' := by intros; simp

private lemma coeffMap_apply (p : MvPolynomial (Fin j) ℚ) : coeffMap j p = p.coeff := rfl

private noncomputable def massMap (n d j : ℕ) : MvPolynomial (Fin j) ℚ →ₗ[ℚ] ℚ :=
  (Finsupp.lsum ℚ (fun e : Fin j →₀ ℕ =>
    (if ∀ i, e i ≤ d then (n : ℚ) ^ (deg e / 2) else 1)⁻¹ •
      (if ∀ i, e i ≤ d then (LinearMap.id : ℚ →ₗ[ℚ] ℚ) else 0))).comp
    (coeffMap j)

private lemma massMap_apply (p : MvPolynomial (Fin j) ℚ) :
    massMap n d j p = ∑ e ∈ p.support,
      if ∀ i, e i ≤ d then p.coeff e / (n : ℚ) ^ (deg e / 2) else 0 := by
  classical
  simp only [massMap, LinearMap.comp_apply, coeffMap_apply,
    Finsupp.lsum_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

private lemma deg_le (e : Fin j →₀ ℕ) (he : ∀ i, e i ≤ d) : deg e ≤ j * d := by
  rw [deg_eq_sum]
  calc
    (∑ i, e i) ≤ ∑ _i : Fin j, d := Finset.sum_le_sum (fun i _ => he i)
    _ = j * d := by simp

private lemma massMap_pow (s : ℕ) :
    massMap n d j (Gt j d ^ s) =
      ∑ m ∈ Finset.range (j * d + 1), gsm j d s m / (n : ℚ) ^ m := by
  classical
  rw [massMap_apply]
  unfold gsm
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hb : ∀ i, e i ≤ d
  · have hEven := (gt_pow_support j d s e he).2
    have hdeg : deg e = 2 * (deg e / 2) := by
      obtain ⟨r, hr⟩ := hEven
      omega
    have hm : deg e / 2 ∈ Finset.range (j * d + 1) := by
      simp only [Finset.mem_range]
      have := deg_le e hb
      omega
    rw [if_pos hb, Finset.sum_eq_single (deg e / 2)]
    · rw [if_pos ⟨hb, hdeg⟩]
    · intro m _ hne
      have hdm : deg e ≠ 2 * m := by omega
      rw [if_neg (fun hc => hdm hc.2), zero_div]
    · exact fun hn => (hn hm).elim
  · simp [hb]

private lemma massMap_pow_nonneg (hn : 1 ≤ n) (s : ℕ) :
    0 ≤ massMap n d j (Gt j d ^ s) := by
  rw [massMap_apply]
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact div_nonneg (gt_coeff_nonneg j d s e) (by positivity)
  · rfl

private lemma massMap_pow_zero (s : ℕ) (hs : j * d < s) :
    massMap n d j (Gt j d ^ s) = 0 := by
  rw [massMap_apply]
  apply Finset.sum_eq_zero
  intro e he
  have hb : ¬∀ i, e i ≤ d := by
    intro hb
    have := deg_le e hb
    have := (gt_pow_support j d s e he).1
    omega
  simp [hb]

private lemma massMap_monomial (e : Fin j →₀ ℕ) (r : ℚ) :
    massMap n d j (MvPolynomial.monomial e r) =
      if ∀ i, e i ≤ d then r / (n : ℚ) ^ (deg e / 2) else 0 := by
  classical
  simp only [massMap, LinearMap.comp_apply, coeffMap_apply,
    MvPolynomial.monomial, AddMonoidAlgebra.coeff_single, Finsupp.lsum_single]
  by_cases hb : ∀ i, e i ≤ d
  · simp [hb, div_eq_mul_inv, mul_comm]
  · simp [hb]

private lemma massMap_one : massMap n d j 1 = 1 := by
  rw [show (1 : MvPolynomial (Fin j) ℚ) = MvPolynomial.monomial 0 1 by simp,
    massMap_monomial]
  simp [deg]

private noncomputable abbrev colExp (a : Fin j → Fin (d + 1)) : Fin j →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))

private noncomputable def colPoly (a : Fin j → Fin (d + 1)) : MvPolynomial (Fin j) ℚ := by
  classical
  exact if Even (∑ i, (a i : ℕ)) then
    MvPolynomial.monomial (colExp a) (((∑ i, (a i : ℕ)) - 1).doubleFactorial : ℚ)
    else 0

private lemma sum_colPoly (j d : ℕ) :
    (∑ a : Fin j → Fin (d + 1), colPoly a) = 1 + Gt j d := by
  classical
  have hsplit (a : Fin j → Fin (d + 1)) : colPoly a =
      (if a = 0 then 1 else 0) +
      (if (∑ i, (a i : ℕ)) ≠ 0 ∧ Even (∑ i, (a i : ℕ)) then
        MvPolynomial.monomial (colExp a) (((∑ i, (a i : ℕ)) - 1).doubleFactorial : ℚ)
        else 0) := by
    by_cases ha : a = 0
    · subst a
      have he : colExp (0 : Fin j → Fin (d + 1)) = 0 := by ext; rfl
      simp [colPoly, he]
    · have hsum : (∑ i, (a i : ℕ)) ≠ 0 := by
        intro h
        apply ha
        funext i
        apply Fin.ext
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp h i
          (Finset.mem_univ _)
      simp [colPoly, ha, hsum]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp [Gt, colExp]

private lemma prod_monomial {α : Type*} [Fintype α] (e : α → Fin j →₀ ℕ) (r : α → ℚ) :
    (∏ a, MvPolynomial.monomial (e a) (r a)) =
      MvPolynomial.monomial (∑ a, e a) (∏ a, r a) := by
  classical
  have h (S : Finset α) : (∏ a ∈ S, MvPolynomial.monomial (e a) (r a)) =
      MvPolynomial.monomial (∑ a ∈ S, e a) (∏ a ∈ S, r a) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih,
        MvPolynomial.monomial_mul]
  exact h Finset.univ

private lemma massMap_colprod (A : Fin n → Fin j → Fin (d + 1)) :
    massMap n d j (∏ a, colPoly (A a)) =
      if ∀ a, Even (∑ i, (A a i : ℕ)) then
        if ∀ i, (∑ a, colExp (A a)) i ≤ d then
          (∏ a, (((∑ i, (A a i : ℕ)) - 1).doubleFactorial : ℚ)) /
            (n : ℚ) ^ (deg (∑ a, colExp (A a)) / 2)
        else 0
      else 0 := by
  classical
  by_cases hA : ∀ a, Even (∑ i, (A a i : ℕ))
  · rw [if_pos hA]
    have hcol (a : Fin n) : colPoly (A a) = MvPolynomial.monomial (colExp (A a))
        (((∑ i, (A a i : ℕ)) - 1).doubleFactorial : ℚ) := by
      simp [colPoly, hA a]
    simp_rw [hcol]
    rw [prod_monomial, massMap_monomial]
  · rw [if_neg hA]
    obtain ⟨a, ha⟩ := not_forall.mp hA
    have hz : (∏ a, colPoly (A a)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) (by simp [colPoly, ha])
    rw [hz, map_zero]

private lemma massMap_colprod_nonneg (A : Fin n → Fin j → Fin (d + 1)) :
    0 ≤ massMap n d j (∏ a, colPoly (A a)) := by
  rw [massMap_colprod]
  split_ifs <;> positivity

private lemma expo_sum (p : Mono n d) : (∑ a, expo p a) = (p.1 : ℕ) := by
  unfold expo
  rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
  exact p.2.property

private lemma expo_le (p : Mono n d) (a : Fin n) : expo p a ≤ d := by
  have h := Multiset.count_le_card a p.2.1
  rw [p.2.property] at h
  exact h.trans (by have := p.1.isLt; omega)

private lemma expo_injective : Function.Injective (fun p : Mono n d => expo p) := by
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

private def encode (v : Fin j → Mono n d) : Fin n → Fin j → Fin (d + 1) :=
  fun a i => ⟨expo (v i) a, Nat.lt_succ_of_le (expo_le (v i) a)⟩

private lemma encode_injective : Function.Injective (encode (n := n) (d := d) (j := j)) := by
  intro v w h
  funext i
  apply expo_injective
  funext a
  exact congrArg Fin.val (congrFun (congrFun h a) i)

private lemma word_moment_le (hn : 1 ≤ n) (v : Fin j → Mono n d) :
    sphMomQ (fun a => ∑ i, expo (v i) a) ≤
      massMap n d j (∏ a, colPoly (encode v a)) := by
  have he (i : Fin j) : (∑ a, colExp (encode v a)) i = (v i).1 := by
    simpa [colExp, encode] using expo_sum (v i)
  have hb : ∀ i, (∑ a, colExp (encode v a)) i ≤ d := by
    intro i
    rw [he]
    have := (v i).1.isLt
    omega
  have hdg : deg (∑ a, colExp (encode v a)) = ∑ a, ∑ i, expo (v i) a := by
    rw [deg_eq_sum, Finset.sum_comm]
    simp [colExp, encode]
  rw [massMap_colprod]
  simp only [encode, hb, implies_true, if_true, hdg]
  exact sphMomQ_le hn _

private lemma massMap_bound (hn : 1 ≤ n) (j d : ℕ) :
    massMap n d j ((1 + Gt j d) ^ n) ≤
      1 + ∑ s ∈ Finset.Icc 1 (j * d), ∑ m ∈ Finset.range (j * d + 1),
        gsm j d s m * (n : ℚ) ^ s / ((n : ℚ) ^ m * (s.factorial : ℚ)) := by
  classical
  let F : ℕ → ℚ := fun s => massMap n d j (Gt j d ^ s)
  have hbin : massMap n d j ((1 + Gt j d) ^ n) =
      ∑ s ∈ Finset.range (n + 1), (n.choose s : ℚ) * F s := by
    rw [add_comm (1 : MvPolynomial (Fin j) ℚ), add_pow]
    simp only [one_pow, mul_one]
    have hc (s : ℕ) : Gt j d ^ s * (n.choose s : MvPolynomial (Fin j) ℚ) =
        (n.choose s : ℚ) • Gt j d ^ s := by
      simp [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_eq_coe_nat, mul_comm]
    simp_rw [hc]
    simp [F, map_sum]
  have htrunc : (∑ s ∈ Finset.range (n + 1), (n.choose s : ℚ) * F s) =
      ∑ s ∈ Finset.range (j * d + 1), (n.choose s : ℚ) * F s := by
    by_cases hnj : n ≤ j * d
    · apply Finset.sum_subset (Finset.range_mono (by omega))
      intro s hs hs'
      have hsn : n < s := by simp only [Finset.mem_range] at hs'; omega
      simp [Nat.choose_eq_zero_of_lt hsn]
    · symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro s hs hs'
      have hsj : j * d < s := by simp only [Finset.mem_range] at hs'; omega
      simp [F, massMap_pow_zero s hsj]
  rw [hbin, htrunc]
  calc
    _ ≤ ∑ s ∈ Finset.range (j * d + 1),
        ((n : ℚ) ^ s / (s.factorial : ℚ)) * F s := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_right (choose_le_pow_div hn s) (massMap_pow_nonneg hn s)
    _ = 1 + ∑ s ∈ Finset.Icc 1 (j * d), ∑ m ∈ Finset.range (j * d + 1),
        gsm j d s m * (n : ℚ) ^ s / ((n : ℚ) ^ m * (s.factorial : ℚ)) := by
      have hset : Finset.range (j * d + 1) = insert 0 (Finset.Icc 1 (j * d)) := by
        ext s; simp; omega
      conv_lhs => rw [hset, Finset.sum_insert (by simp)]
      have hzero : ((n : ℚ) ^ 0 / (Nat.factorial 0 : ℚ)) * F 0 = 1 := by
        simp [F, massMap_one]
      rw [hzero]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      dsimp [F]
      rw [massMap_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

private lemma raw_mass_le (hn : 1 ≤ n) (j : ℕ) :
    (∑ v : Fin j → Mono n d, sphMomQ (fun a => ∑ i, expo (v i) a)) ≤
      massMap n d j ((1 + Gt j d) ^ n) := by
  classical
  let W : (Fin n → Fin j → Fin (d + 1)) → ℚ :=
    fun A => massMap n d j (∏ a, colPoly (A a))
  have heq : (∑ A, W A) = massMap n d j ((1 + Gt j d) ^ n) := by
    rw [← map_sum]
    congr 1
    rw [← Fintype.sum_pow, sum_colPoly]
  rw [← heq]
  calc
    _ ≤ ∑ v : Fin j → Mono n d, W (encode v) :=
      Finset.sum_le_sum (fun v _ => word_moment_le hn v)
    _ = ∑ A ∈ Finset.univ.image encode, W A := by
      rw [Finset.sum_image]
      exact fun a _ b _ h => encode_injective h
    _ ≤ ∑ A, W A := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun A _ _ => massMap_colprod_nonneg A)

private lemma traced_mass_le_raw (hn : 1 ≤ n) (j l : ℕ) (hjl : 2 * l < j) :
    massH n d j l ≤
      ((∑ v : Fin j → Mono n d, sphMomQ (fun a => ∑ i, expo (v i) a) : ℚ) : ℝ) := by
  classical
  let α := (Fin l ⊕ Fin l) ⊕ Fin (j - 2 * l)
  let e : α ≃ Fin j := Fintype.equivOfCardEq (by simp [α]; omega)
  let pack : ((Fin (j - 2 * l) → Mono n d) × (Fin l → Mono n d)) →
      (Fin j → Mono n d) :=
    fun p i => Sum.elim (Sum.elim p.2 p.2) p.1 (e.symm i)
  have hexp (p : (Fin (j - 2 * l) → Mono n d) × (Fin l → Mono n d)) (a : Fin n) :
      (∑ i, expo (pack p i) a) =
        (∑ t, 2 * expo (p.2 t) a) + ∑ t, expo (p.1 t) a := by
    have ht := (e.sum_comp (fun i => expo (pack p i) a)).symm
    dsimp [α] at ht
    simp only [pack, Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr] at ht
    rw [ht, ← Finset.mul_sum]
    ring
  have hinj : Function.Injective pack := by
    intro p q hpq
    apply Prod.ext
    · funext t
      simpa [pack] using congrFun hpq (e (Sum.inr t))
    · funext t
      simpa [pack] using congrFun hpq (e (Sum.inl (Sum.inl t)))
  let V : (Fin j → Mono n d) → ℚ := fun v => sphMomQ (fun a => ∑ i, expo (v i) a)
  have hsum : (∑ w : Fin (j - 2 * l) → Mono n d, HQ l w) =
      ∑ p : (Fin (j - 2 * l) → Mono n d) × (Fin l → Mono n d), V (pack p) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro w _
    unfold HQ
    apply Finset.sum_congr rfl
    intro c _
    dsimp [V]
    congr 1
    funext a
    exact (hexp (w, c) a).symm
  have hle : (∑ w : Fin (j - 2 * l) → Mono n d, HQ l w) ≤ ∑ v, V v := by
    rw [hsum]
    calc
      _ = ∑ v ∈ Finset.univ.image pack, V v := by
        rw [Finset.sum_image]
        exact fun a _ b _ h => hinj h
      _ ≤ ∑ v, V v := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun v _ _ => sphMomQ_nonneg hn _)
  have hHQ (w : Fin (j - 2 * l) → Mono n d) : 0 ≤ (HQ l w : ℝ) := by
    have hq : (0 : ℚ) ≤ HQ l w := by
      unfold HQ
      exact Finset.sum_nonneg (fun c _ => sphMomQ_nonneg hn _)
    exact_mod_cast hq
  unfold massH
  simp_rw [abs_of_nonneg (hHQ _)]
  exact_mod_cast hle

private lemma top_words {α : Type*} [Fintype α] [DecidableEq α]
    (H : α → ℝ) (hH : ∀ a, 0 ≤ H a) (O : ℕ) (hO : 1 ≤ O) :
    ∃ A : Finset α, A.card ≤ O ∧
      (∑ a ∈ Finset.univ \ A, H a ^ 2) ≤ (∑ a, H a) ^ 2 / (4 * O) := by
  classical
  let C := (Finset.univ : Finset α).powerset.filter (fun A => A.card ≤ O)
  have hC : C.Nonempty := ⟨∅, by simp [C]⟩
  obtain ⟨A, hAC, hmax⟩ := C.exists_max_image (fun A => ∑ a ∈ A, H a) hC
  have hAO : A.card ≤ O := (Finset.mem_filter.mp hAC).2
  have hins (a : α) (ha : a ∉ A) (hcard : A.card < O) : H a = 0 := by
    have hi : insert a A ∈ C := by
      simp only [C, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
      rw [Finset.card_insert_of_notMem ha]
      omega
    have hh := hmax _ hi
    rw [Finset.sum_insert ha] at hh
    linarith [hH a]
  have hswap (a b : α) (ha : a ∉ A) (hb : b ∈ A) : H a ≤ H b := by
    have hi : insert a (A.erase b) ∈ C := by
      simp only [C, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
      rw [Finset.card_insert_of_notMem (by simp [ha]), Finset.card_erase_of_mem hb]
      omega
    have hh := hmax _ hi
    rw [Finset.sum_insert (by simp [ha])] at hh
    have he := Finset.sum_erase_add A H hb
    linarith
  let T : ℝ := ∑ a ∈ A, H a
  let U : ℝ := ∑ a ∈ Finset.univ \ A, H a
  have hT : 0 ≤ T := Finset.sum_nonneg (fun a _ => hH a)
  have hU : 0 ≤ U := Finset.sum_nonneg (fun a _ => hH a)
  have htotal : (∑ a, H a) = T + U := by
    dsimp [T, U]
    exact (Finset.sum_sdiff (Finset.subset_univ A)).symm.trans (add_comm _ _)
  have hpoint (a : α) (ha : a ∉ A) : (O : ℝ) * H a ≤ T := by
    by_cases hc : A.card < O
    · rw [hins a ha hc]; simpa using hT
    · have hc' : A.card = O := by omega
      have hh := Finset.sum_le_sum (fun b hb => hswap a b ha hb)
      simpa [T, hc', mul_comm] using hh
  have hsum : (O : ℝ) * (∑ a ∈ Finset.univ \ A, H a ^ 2) ≤ T * U := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have hp := mul_le_mul_of_nonneg_right (hpoint a (Finset.mem_sdiff.mp ha).2) (hH a)
    nlinarith
  have hOp : (0 : ℝ) < O := by exact_mod_cast hO
  refine ⟨A, hAO, (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * O)).mpr ?_⟩
  rw [htotal]
  nlinarith [sq_nonneg (T - U)]

/-- **Lemma `mass`**: `S_{j,l}(n) ≤ Ŝ_j(n)` (`s = j − 2l ≥ 1`). -/
theorem mass_le (hn : 1 ≤ n) (hd : 1 ≤ d) (j l : ℕ) (hjl : 2 * l < j) :
    massH n d j l ≤ Shat j d n := by
  have hraw := raw_mass_le (d := d) hn j
  have hbound := massMap_bound hn j d
  have hq := hraw.trans hbound
  have hr : ((∑ v : Fin j → Mono n d,
      sphMomQ (fun a => ∑ i, expo (v i) a) : ℚ) : ℝ) ≤ Shat j d n := by
    unfold Shat
    exact_mod_cast hq
  exact (traced_mass_le_raw hn j l hjl).trans hr

/-- **Lemma `tail`** (orbits): for a symmetric `H ≥ 0` of order `s` and `1 ≤ O`, some set of at most `O`
orbits leaves a residual with `‖R‖² ≤ (Σ_w H w)²/(4O)`; if `O` is at least the number of orbits, one
leaves `R = 0`. -/
theorem tail_le {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ} (H : (Fin s → ι) → ℝ)
    (hH : ∀ w, 0 ≤ H w) (hsym : IsSymmT H) (O : ℕ) (hO : 1 ≤ O) :
    ∃ K : Finset (Multiset ι), K.card ≤ O ∧ (∀ o ∈ K, Multiset.card o = s) ∧
      frob (fun w => if mset w ∈ K then 0 else H w) ≤ (∑ w, H w) ^ 2 / (4 * O) ∧
      (Fintype.card (Sym ι s) ≤ O → frob (fun w => if mset w ∈ K then 0 else H w) = 0) := by
  classical
  have hm (w : Fin s → ι) : Multiset.card (mset w) = s := by simp [mset]
  let all : Finset (Multiset ι) := Finset.univ.image (fun q : Sym ι s => (q : Multiset ι))
  have hall (w : Fin s → ι) : mset w ∈ all :=
    Finset.mem_image.mpr ⟨⟨mset w, hm w⟩, Finset.mem_univ _, rfl⟩
  have hac : all.card ≤ Fintype.card (Sym ι s) :=
    (Finset.card_image_le).trans (by simp)
  have has : ∀ o ∈ all, Multiset.card o = s := by
    intro o ho
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ho
    exact q.property
  by_cases hc : Fintype.card (Sym ι s) ≤ O
  · refine ⟨all, hac.trans hc, has, ?_, ?_⟩
    · simp only [frob, ite_eq_left (hall _), zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
      positivity
    · intro _
      simp [frob, hall]
  · obtain ⟨A, hAO, hA⟩ := top_words H hH O hO
    refine ⟨A.image mset, (Finset.card_image_le).trans hAO, ?_, ?_, fun h => (hc h).elim⟩
    · intro o ho
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp ho
      exact hm w
    · apply le_trans _ hA
      simp only [frob, ite_pow, zero_pow (by decide : 2 ≠ 0)]
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, zero_add]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro w hw
        have hw' := (Finset.mem_filter.mp hw).2
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro ha
        exact hw' (Finset.mem_image.mpr ⟨w, ha, rfl⟩)
      · intro w _ _
        positivity

/-- **The kept sets exist** (Lemma `C`, tail clause). -/
theorem kept_exists (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hτ : 0 < tauF n d k)
    (j l : ℕ) (hjl : (j, l) ∈ levels k) : ∃ K, KeepOK n d k ε j l K := by
  classical
  have hj : 2 * l < j := by
    simpa [levels] using (Finset.mem_filter.mp hjl).2
  let s := j - 2 * l
  let H : (Fin s → Mono n d) → ℝ := fun w => |(HQ l w : ℝ)|
  let B : ℝ := Shat j d n
  let E : ℝ := tauF n d k * epsS ε * (s : ℕ) * 4 ^ l /
    (n : ℝ) ^ (k - s)
  have hs : 0 < s := by dsimp [s]; omega
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have heps : 0 < epsS ε := by unfold epsS; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hH : ∀ w, 0 ≤ H w := fun w => abs_nonneg _
  have hmass : (∑ w, H w) ≤ B := mass_le hn hd j l hj
  have hB : 0 ≤ B := (Finset.sum_nonneg (fun w _ => hH w)).trans hmass
  have hentry (w : Fin s → Mono n d) : H w ≤ B :=
    (Finset.single_le_sum (fun w _ => hH w) (Finset.mem_univ w)).trans hmass
  have hsym : IsSymmT H := by
    intro σ w
    dsimp [H, HQ]
    congr 3
    funext c
    congr 1
    funext a
    congr 1
    exact Equiv.sum_comp σ (fun t => expo (w t) a)
  let q : ℕ := ⌈B ^ 2 / (4 * E)⌉₊
  have hceil : B ^ 2 / (4 * E) ≤ (q : ℝ) := Nat.le_ceil _
  have halloc : Ocnt n d k ε j l = min (Fintype.card (Sym (Mono n d) s)) q := by
    unfold Ocnt
    apply congrArg (fun r : ℝ => min (Fintype.card (Sym (Mono n d) s)) ⌈r⌉₊)
    dsimp [q, B, E, s]
    field_simp
  by_cases hq : q = 0
  · have hB0 : B = 0 := by
      rw [hq, Nat.cast_zero] at hceil
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * E)).mp hceil
      nlinarith [sq_nonneg B]
    have hzero (w : Fin s → Mono n d) : (HQ l w : ℝ) = 0 := by
      have := hentry w
      dsimp [H] at this
      rw [hB0] at this
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    refine ⟨∅, ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa [frob, RQ, HKQ, hzero] using hE.le
  · have hqp : 1 ≤ q := by omega
    obtain ⟨K, hKq, hKs, hKt, _⟩ := tail_le H hH hsym q hqp
    have hKcard : K.card ≤ Fintype.card (Sym (Mono n d) s) := by
      let all : Finset (Multiset (Mono n d)) :=
        Finset.univ.image (fun o : Sym (Mono n d) s => (o : Multiset (Mono n d)))
      have hsub : K ⊆ all := by
        intro o ho
        exact Finset.mem_image.mpr ⟨⟨o, hKs o ho⟩, Finset.mem_univ _, rfl⟩
      exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
    refine ⟨K, ?_, hKs, ?_⟩
    · rw [halloc]
      exact le_min hKcard hKq
    · have hqpR : (0 : ℝ) < q := by exact_mod_cast hqp
      have hsq : (∑ w, H w) ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg (fun w _ => hH w)) hmass 2
      have hbound : B ^ 2 / (4 * q) ≤ E := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * q)).mpr
        have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * E)).mp hceil
        nlinarith
      have hr : frob (fun w : Fin s → Mono n d => (RQ K l w : ℝ)) =
          frob (fun w => if mset w ∈ K then 0 else H w) := by
        unfold frob
        apply Finset.sum_congr rfl
        intro w _
        by_cases hw : mset w ∈ K
        · simp [RQ, HKQ, hw]
        · simp [RQ, HKQ, hw, H, sq_abs]
      rw [hr]
      exact hKt.trans ((div_le_div_of_nonneg_right hsq (by positivity)).trans hbound)

end BstLean.Part41

