import BstLean.Part86Defs
import BstLean.Part53Cost_Orbits

/-!
# Part 86, slice operator bound, algebra: a homogeneous polynomial under a rotation and the split
of the first coordinate

`claimJ`: let `e` be the monomial coefficients of a homogeneous polynomial `q` of degree `j` on
`ℝ^{m+1}`, `O` a matrix with orthonormal rows, `q(O e₀) = 0`. Then `ω ↦ q(O (S, R ω))` is a
polynomial in `ω ∈ ℝ^m` with no constant term whose monomial coefficient vector `a` has
`‖a‖² ≤ j! R² ‖e‖²`.
-/

namespace BstLean.Part86.SliceOpA

open BstLean.Part36 (monoVal)
open BstLean.Part41 (Mono phiM mset wordOf)
open BstLean.Part53.CostAux (orbitCount mset_wordOf orbitCount_multinomial)

/-! ## Words and multisets -/

section words

variable {α : Type} [Fintype α] [DecidableEq α] {j : ℕ}

/-- The multiset of a word, as an element of `Sym α j`. -/
def symOf (τ : Fin j → α) : Sym α j := ⟨mset τ, by simp [mset]⟩

/-- The words of a multiset. -/
def fiber (β : Sym α j) : Finset (Fin j → α) :=
  (Finset.univ : Finset (Fin j → α)).filter (fun w => mset w = β.val)

lemma mem_fiber (β : Sym α j) (τ : Fin j → α) : τ ∈ fiber β ↔ symOf τ = β := by
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, symOf]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h

lemma card_fiber (β : Sym α j) : (fiber β).card = orbitCount β := by
  unfold fiber orbitCount
  congr

lemma sum_fiber (F : (Fin j → α) → ℝ) :
    ∑ τ, F τ = ∑ β : Sym α j, ∑ τ ∈ fiber β, F τ := by
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin j → α)) symOf F]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext τ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_fiber]

lemma fiber_pos [Inhabited α] (β : Sym α j) : 0 < (fiber β).card := by
  apply Finset.card_pos.mpr
  refine ⟨wordOf j β.val, ?_⟩
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
  exact mset_wordOf j β.val β.property

lemma fiber_le (β : Sym α j) : ((fiber β).card : ℝ) ≤ (j.factorial : ℝ) := by
  rw [card_fiber, orbitCount_multinomial]
  have h : β.val.toFinsupp.multinomial ≤ j.factorial := by
    unfold Finsupp.multinomial
    rw [Multiset.toFinsupp_sum_eq, β.property]
    exact Nat.div_le_self _ _
  exact_mod_cast h

lemma monoVal_mset {n : ℕ} (y : Fin n → ℝ) (τ : Fin j → Fin n) :
    monoVal y (mset τ) = ∏ t, y (τ t) := by
  simp only [monoVal, mset, Multiset.map_map, Function.comp_def]
  rfl

end words

/-! ## The tensor of a coefficient vector -/

section tensor

variable {N j : ℕ}

/-- The (symmetric) tensor of a coefficient vector. -/
noncomputable def tens (e : Sym (Fin N) j → ℝ) (τ : Fin j → Fin N) : ℝ :=
  e (symOf τ) / ((fiber (symOf τ)).card : ℝ)

lemma tens_contr [Inhabited (Fin N)] (e : Sym (Fin N) j → ℝ) (y : Fin N → ℝ) :
    ∑ τ, tens e τ * ∏ t, y (τ t) = ∑ β : Sym (Fin N) j, e β * monoVal y β.val := by
  rw [sum_fiber]
  apply Finset.sum_congr rfl
  intro β _
  have hpos : (0 : ℝ) < ((fiber β).card : ℝ) := by exact_mod_cast fiber_pos β
  have h : ∀ τ ∈ fiber β, tens e τ * ∏ t, y (τ t) =
      e β / ((fiber β).card : ℝ) * monoVal y β.val := by
    intro τ hτ
    have hs := (mem_fiber β τ).mp hτ
    have hm : mset τ = β.val := congrArg Subtype.val hs
    rw [tens, hs, ← monoVal_mset, hm]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  field_simp

lemma tens_frob [Inhabited (Fin N)] (e : Sym (Fin N) j → ℝ) :
    ∑ τ, tens e τ ^ 2 ≤ ∑ β : Sym (Fin N) j, e β ^ 2 := by
  rw [sum_fiber]
  apply Finset.sum_le_sum
  intro β _
  have hpos : (1 : ℝ) ≤ ((fiber β).card : ℝ) := by exact_mod_cast fiber_pos β
  have h : ∀ τ ∈ fiber β, tens e τ ^ 2 = (e β / ((fiber β).card : ℝ)) ^ 2 := by
    intro τ hτ
    have hs := (mem_fiber β τ).mp hτ
    rw [tens, hs]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  have h0 : (0 : ℝ) < ((fiber β).card : ℝ) := by linarith
  have : ((fiber β).card : ℝ) * (e β / ((fiber β).card : ℝ)) ^ 2 =
      e β ^ 2 / ((fiber β).card : ℝ) := by field_simp
  rw [this]
  exact div_le_self (sq_nonneg _) hpos

/-- The rotated tensor. -/
def rotT (O : Fin N → Fin N → ℝ) (T : (Fin j → Fin N) → ℝ) (τ' : Fin j → Fin N) : ℝ :=
  ∑ τ, T τ * ∏ t, O (τ t) (τ' t)

lemma rot_contr (O : Fin N → Fin N → ℝ) (T : (Fin j → Fin N) → ℝ) (y : Fin N → ℝ) :
    ∑ τ', rotT O T τ' * ∏ t, y (τ' t) = ∑ τ, T τ * ∏ t, ∑ l, O (τ t) l * y l := by
  simp only [rotT, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  have h := Finset.prod_univ_sum (fun (_ : Fin j) => (Finset.univ : Finset (Fin N)))
    (fun t l => O (τ t) l * y l)
  rw [h, Fintype.piFinset_univ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ' _
  rw [Finset.prod_mul_distrib]
  ring

lemma rot_frob (O : Fin N → Fin N → ℝ)
    (hrow : ∀ i i', ∑ l, O i l * O i' l = if i = i' then 1 else 0)
    (T : (Fin j → Fin N) → ℝ) :
    ∑ τ', rotT O T τ' ^ 2 = ∑ τ, T τ ^ 2 := by
  have h1 : ∀ τ' : Fin j → Fin N, rotT O T τ' ^ 2 =
      ∑ τ, ∑ σ, T τ * T σ * ∏ t, (O (τ t) (τ' t) * O (σ t) (τ' t)) := by
    intro τ'
    rw [pow_two, rotT, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.prod_mul_distrib]
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ τ : Fin j → Fin N,
      ∑ τ' : Fin j → Fin N, ∑ σ, T τ * T σ * ∏ t, (O (τ t) (τ' t) * O (σ t) (τ' t)) =
        T τ ^ 2 := by
    intro τ
    rw [Finset.sum_comm]
    have h3 : ∀ σ : Fin j → Fin N,
        ∑ τ' : Fin j → Fin N, T τ * T σ * ∏ t, (O (τ t) (τ' t) * O (σ t) (τ' t)) =
          T τ * T σ * (if τ = σ then 1 else 0) := by
      intro σ
      rw [← Finset.mul_sum]
      congr 1
      have h := Finset.prod_univ_sum (fun (_ : Fin j) => (Finset.univ : Finset (Fin N)))
        (fun t l => O (τ t) l * O (σ t) l)
      rw [Fintype.piFinset_univ] at h
      rw [← h]
      simp only [hrow]
      rw [Finset.prod_boole]
      simp only [Finset.mem_univ, forall_const, funext_iff]
    simp only [h3]
    rw [Finset.sum_eq_single τ]
    · simp [pow_two]
    · intro σ _ hσ
      simp [Ne.symm hσ]
    · intro h; exact absurd (Finset.mem_univ τ) h
  exact Finset.sum_congr rfl (fun τ _ => h2 τ)

/-- The monomial coefficients of an ordered tensor. -/
def coefT (T : (Fin j → Fin N) → ℝ) (β : Sym (Fin N) j) : ℝ := ∑ τ ∈ fiber β, T τ

lemma coefT_contr (T : (Fin j → Fin N) → ℝ) (y : Fin N → ℝ) :
    ∑ β : Sym (Fin N) j, coefT T β * monoVal y β.val = ∑ τ, T τ * ∏ t, y (τ t) := by
  rw [sum_fiber]
  apply Finset.sum_congr rfl
  intro β _
  rw [coefT, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro τ hτ
  have hm : mset τ = β.val := congrArg Subtype.val ((mem_fiber β τ).mp hτ)
  rw [← monoVal_mset, hm]

lemma coefT_frob (T : (Fin j → Fin N) → ℝ) :
    ∑ β : Sym (Fin N) j, coefT T β ^ 2 ≤ (j.factorial : ℝ) * ∑ τ, T τ ^ 2 := by
  rw [sum_fiber (fun τ => T τ ^ 2), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro β _
  have h := sq_sum_le_card_mul_sum_sq (s := fiber β) (f := T)
  have h2 : 0 ≤ ∑ τ ∈ fiber β, T τ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc coefT T β ^ 2 ≤ ((fiber β).card : ℝ) * ∑ τ ∈ fiber β, T τ ^ 2 := h
    _ ≤ (j.factorial : ℝ) * ∑ τ ∈ fiber β, T τ ^ 2 :=
      mul_le_mul_of_nonneg_right (fiber_le β) h2

end tensor

/-! ## Splitting off the first coordinate -/

section split

variable {m : ℕ}

/-- The predecessor of a nonzero index. -/
def predO (i : Fin (m + 1)) : Option (Fin m) := if h : i = 0 then none else some (i.pred h)

lemma predO_zero : predO (0 : Fin (m + 1)) = none := by simp [predO]

lemma predO_succ (a : Fin m) : predO (Fin.succ a) = some a := by
  simp [predO, Fin.succ_ne_zero]

lemma monoVal_cons_split (S R : ℝ) (ω : Fin m → ℝ) (s : Multiset (Fin (m + 1))) :
    monoVal (Fin.cons S (R • ω) : Fin (m + 1) → ℝ) s =
      S ^ s.count 0 * R ^ (s.filterMap predO).card * monoVal ω (s.filterMap predO) := by
  induction s using Multiset.induction_on with
  | empty => simp [monoVal]
  | cons a s ih =>
    have hc : monoVal (Fin.cons S (R • ω) : Fin (m + 1) → ℝ) (a ::ₘ s) =
        (Fin.cons S (R • ω) : Fin (m + 1) → ℝ) a *
          monoVal (Fin.cons S (R • ω) : Fin (m + 1) → ℝ) s := by
      simp [monoVal]
    rw [hc, ih]
    rcases Fin.eq_zero_or_eq_succ a with h | ⟨a', h⟩
    · subst h
      rw [Multiset.filterMap_cons_none _ _ predO_zero, Multiset.count_cons_self, Fin.cons_zero]
      ring
    · subst h
      rw [Multiset.filterMap_cons_some _ _ _ (predO_succ a'),
        Multiset.count_cons_of_ne (Fin.succ_ne_zero a').symm, Fin.cons_succ,
        Multiset.card_cons]
      have : monoVal ω (a' ::ₘ s.filterMap predO) = ω a' * monoVal ω (s.filterMap predO) := by
        simp [monoVal]
      rw [this]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

lemma decomp (s : Multiset (Fin (m + 1))) :
    s = (s.filterMap predO).map Fin.succ + Multiset.replicate (s.count 0) 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rcases Fin.eq_zero_or_eq_succ a with h | ⟨a', h⟩
    · subst h
      rw [Multiset.filterMap_cons_none _ _ predO_zero, Multiset.count_cons_self,
        Multiset.replicate_succ, Multiset.add_cons, ← ih]
    · subst h
      rw [Multiset.filterMap_cons_some _ _ _ (predO_succ a'),
        Multiset.count_cons_of_ne (Fin.succ_ne_zero a').symm, Multiset.map_cons,
        Multiset.cons_add, ← ih]

lemma card_decomp (s : Multiset (Fin (m + 1))) :
    s.card = (s.filterMap predO).card + s.count 0 := by
  conv_lhs => rw [decomp s]
  simp

lemma all_zero_of_card (s : Multiset (Fin (m + 1))) (h : (s.filterMap predO).card = 0) :
    ∀ a ∈ s, a = 0 := by
  intro a ha
  have h0 : s.filterMap predO = 0 := Multiset.card_eq_zero.mp h
  have hd := decomp s
  rw [h0] at hd
  rw [hd] at ha
  simp only [Multiset.map_zero, zero_add] at ha
  exact Multiset.eq_of_mem_replicate ha

variable {j d : ℕ}

/-- The monomial in `ω` of a monomial in `(S, R ω)`. -/
def gam (hjd : j ≤ d) (β : Sym (Fin (m + 1)) j) : Mono m d :=
  ⟨⟨(β.val.filterMap predO).card, by
    have := card_decomp β.val
    have := β.property
    omega⟩, ⟨β.val.filterMap predO, rfl⟩⟩

lemma gam_val (hjd : j ≤ d) (β : Sym (Fin (m + 1)) j) :
    ((gam hjd β).2 : Multiset (Fin m)) = β.val.filterMap predO := rfl

lemma gam_inj (hjd : j ≤ d) : Function.Injective (gam (m := m) hjd) := by
  intro β1 β2 h
  have h1 : β1.val.filterMap predO = β2.val.filterMap predO := by
    have := congrArg (fun q : Mono m d => (q.2 : Multiset (Fin m))) h
    simpa only [gam_val] using this
  have c1 := card_decomp β1.val
  have c2 := card_decomp β2.val
  rw [β1.property] at c1
  rw [β2.property] at c2
  rw [h1] at c1
  have hc : β1.val.count 0 = β2.val.count 0 := by omega
  apply Subtype.ext
  rw [decomp β1.val, decomp β2.val, h1, hc]

lemma gam_default (hjd : j ≤ d) (β : Sym (Fin (m + 1)) j)
    (h : gam hjd β = default) : (β.val.filterMap predO).card = 0 := by
  have := congrArg (fun q : Mono m d => (q.1 : ℕ)) h
  exact this

end split

/-! ## Sums over an injective map -/

lemma inj_sum_sq {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (f : A → B)
    (hf : Function.Injective f) (t : A → ℝ) :
    ∑ q : B, (∑ β : A, if f β = q then t β else 0) ^ 2 = ∑ β : A, t β ^ 2 := by
  have h : ∀ q : B, (∑ β : A, if f β = q then t β else 0) ^ 2 =
      ∑ β : A, if f β = q then t β ^ 2 else 0 := by
    intro q
    by_cases hq : ∃ β0, f β0 = q
    · obtain ⟨β0, hβ0⟩ := hq
      rw [Finset.sum_eq_single β0, Finset.sum_eq_single β0]
      · simp [hβ0]
      · intro β _ hβ
        have : f β ≠ q := fun h' => hβ (hf (h'.trans hβ0.symm))
        simp [this]
      · intro h'; exact absurd (Finset.mem_univ β0) h'
      · intro β _ hβ
        have : f β ≠ q := fun h' => hβ (hf (h'.trans hβ0.symm))
        simp [this]
      · intro h'; exact absurd (Finset.mem_univ β0) h'
    · push Not at hq
      simp [hq]
  simp only [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  simp

/-! ## The claim at degree `j` -/

theorem claimJ (m j d : ℕ) (hjd : j ≤ d) (e : Sym (Fin (m + 1)) j → ℝ)
    (O : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hrow : ∀ i i', ∑ l, O i l * O i' l = if i = i' then 1 else 0)
    (hv0 : ∑ β : Sym (Fin (m + 1)) j, e β * monoVal (fun i => O i 0) β.val = 0)
    (S R : ℝ) (hS : |S| ≤ 1) (hR0 : 0 ≤ R) (hR1 : R ≤ 1) :
    ∃ a : Mono m d → ℝ, a default = 0 ∧
      ∑ q, a q ^ 2 ≤ (j.factorial : ℝ) * R ^ 2 * ∑ β : Sym (Fin (m + 1)) j, e β ^ 2 ∧
      ∀ ω : Fin m → ℝ,
        ∑ β : Sym (Fin (m + 1)) j, e β *
            monoVal (fun i => ∑ l, O i l * (Fin.cons S (R • ω) : Fin (m + 1) → ℝ) l) β.val =
          ∑ q, a q * phiM ω q := by
  classical
  set T := tens e with hT
  set T' := rotT O T with hT'
  set c' := coefT T' with hc'
  -- the value at the constant word
  have hconst : T' (fun _ => 0) = 0 := by
    have h := tens_contr e (fun i => O i 0)
    rw [hv0] at h
    simpa only [hT', rotT] using h
  have hzero : ∀ β : Sym (Fin (m + 1)) j, (β.val.filterMap predO).card = 0 → c' β = 0 := by
    intro β hβ
    have hall := all_zero_of_card β.val hβ
    rw [hc', coefT]
    apply Finset.sum_eq_zero
    intro τ hτ
    have hm : mset τ = β.val := congrArg Subtype.val ((mem_fiber β τ).mp hτ)
    have : τ = fun _ => 0 := by
      funext t
      apply hall
      rw [← hm, mset]
      exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val t)
    rw [this, hconst]
  let tt : Sym (Fin (m + 1)) j → ℝ := fun β =>
    c' β * (S ^ β.val.count 0 * R ^ (β.val.filterMap predO).card)
  refine ⟨fun q => ∑ β : Sym (Fin (m + 1)) j, if gam hjd β = q then tt β else 0, ?_, ?_, ?_⟩
  · apply Finset.sum_eq_zero
    intro β _
    by_cases h : gam hjd β = default
    · simp only [h, ite_true, tt]
      rw [hzero β (gam_default hjd β h), zero_mul]
    · simp [h]
  · rw [inj_sum_sq (gam hjd) (gam_inj hjd) tt]
    have hS2 : S ^ 2 ≤ 1 := by
      have := abs_nonneg S
      rw [← sq_abs]; nlinarith
    have h1 : ∀ β : Sym (Fin (m + 1)) j, tt β ^ 2 ≤ R ^ 2 * c' β ^ 2 := by
      intro β
      by_cases hb : (β.val.filterMap predO).card = 0
      · simp only [tt]
        rw [hzero β hb]
        simp
      · obtain ⟨b, hb'⟩ := Nat.exists_eq_succ_of_ne_zero hb
        simp only [tt]
        rw [hb']
        have hSz : (S ^ β.val.count 0) ^ 2 ≤ 1 := by
          rw [← pow_mul, mul_comm, pow_mul]
          exact pow_le_one₀ (sq_nonneg S) hS2
        have hRb : (R ^ b) ^ 2 ≤ 1 := by
          rw [← pow_mul]
          exact pow_le_one₀ hR0 hR1
        have e1 : (c' β * (S ^ β.val.count 0 * R ^ (b + 1))) ^ 2 =
            R ^ 2 * c' β ^ 2 * ((S ^ β.val.count 0) ^ 2 * (R ^ b) ^ 2) := by ring
        rw [e1]
        have : (S ^ β.val.count 0) ^ 2 * (R ^ b) ^ 2 ≤ 1 := by
          calc (S ^ β.val.count 0) ^ 2 * (R ^ b) ^ 2 ≤ 1 * 1 :=
                mul_le_mul hSz hRb (sq_nonneg _) (by norm_num)
            _ = 1 := by ring
        have h0 : 0 ≤ R ^ 2 * c' β ^ 2 := by positivity
        nlinarith
    calc ∑ β, tt β ^ 2 ≤ ∑ β, R ^ 2 * c' β ^ 2 := Finset.sum_le_sum (fun β _ => h1 β)
      _ = R ^ 2 * ∑ β, c' β ^ 2 := by rw [Finset.mul_sum]
      _ ≤ R ^ 2 * ((j.factorial : ℝ) * ∑ τ, T' τ ^ 2) :=
        mul_le_mul_of_nonneg_left (coefT_frob T') (sq_nonneg R)
      _ = R ^ 2 * ((j.factorial : ℝ) * ∑ τ, T τ ^ 2) := by rw [hT', rot_frob O hrow T]
      _ ≤ R ^ 2 * ((j.factorial : ℝ) * ∑ β, e β ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg R)
        exact mul_le_mul_of_nonneg_left (tens_frob e) (by positivity)
      _ = (j.factorial : ℝ) * R ^ 2 * ∑ β, e β ^ 2 := by ring
  · intro ω
    set y : Fin (m + 1) → ℝ := Fin.cons S (R • ω) with hy
    rw [← tens_contr e, ← rot_contr O T y, ← coefT_contr]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    have : ∀ q : Mono m d, (if gam hjd β = q then tt β else 0) * phiM ω q =
        if gam hjd β = q then tt β * phiM ω (gam hjd β) else 0 := by
      intro q
      by_cases h : gam hjd β = q
      · simp [h]
      · simp [h]
    simp only [this]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true, tt]
    rw [hy, monoVal_cons_split]
    have : phiM ω (gam hjd β) = monoVal ω (β.val.filterMap predO) := rfl
    rw [this]
    ring

end BstLean.Part86.SliceOpA

#print axioms BstLean.Part86.SliceOpA.claimJ
