import BstLean.Part74GenDefs
import BstLean.Part74Stein
import BstLean.Part74Eval
import BstLean.Part74K33
import BstLean.Part71SH

/-!
# Part 74: the generic engine theorem for lists of terms, and the weights at `(3, 3)`

* `polyPN v L`: the polynomial of a list of terms with natural coefficients; `polyPN_mulL`,
  `polyPN_powL`.
* `surrL74`: the surrogate expectation of `polyPN v L` is the engine output `IL74` (all degrees
  even and `≤ 2D`, or all degrees odd).
* `weights33_74`: at every key with `2l ≤ i`, `w33 n K t v κ = wRK (surrRK n K t v) 3 v κ`.
-/

namespace BstLean.Part74

open MeasureTheory MvPolynomial
open BstLean.Part56 BstLean.Part56.MomProg
open BstLean.Part69

variable {n : ℕ}

/-! ## The polynomial of a list of terms -/

/-- The polynomial of one term. -/
noncomputable def trmP (v : Fin n → ℝ) (t : TrmN) : MvPolynomial (Fin n) ℝ :=
  C (t.1 : ℝ) * (Sp v 1 1 ^ t.2.1 * monP v t.2.2)

/-- The polynomial `Σ_t c_t s^{e_t} Π_{(a,b) ∈ M_t} S_{a,b}`. -/
noncomputable def polyPN (v : Fin n → ℝ) (L : List TrmN) : MvPolynomial (Fin n) ℝ :=
  (L.map fun t => C (t.1 : ℝ) * (Sp v 1 1 ^ t.2.1 * monP v t.2.2)).sum

theorem polyPN_nil (v : Fin n → ℝ) : polyPN v [] = 0 := by simp [polyPN]

theorem polyPN_cons (v : Fin n → ℝ) (t : TrmN) (L : List TrmN) :
    polyPN v (t :: L) = trmP v t + polyPN v L := by simp [polyPN, trmP]

theorem polyPN_append (v : Fin n → ℝ) (L1 L2 : List TrmN) :
    polyPN v (L1 ++ L2) = polyPN v L1 + polyPN v L2 := by simp [polyPN]

theorem polyPN_eval (v x : Fin n → ℝ) (L : List TrmN) :
    eval x (polyPN v L) = (L.map fun t => (t.1 : ℝ) * ((∑ i, v i * x i) ^ t.2.1 *
      (t.2.2.map fun ab => ∑ i, v i ^ ab.1 * x i ^ ab.2).prod)).sum := by
  induction L with
  | nil => simp [polyPN_nil]
  | cons t ts ih =>
    rw [polyPN_cons, eval_add, ih, List.map_cons, List.sum_cons, trmP, eval_mul,
      eval_C, eval_mul, eval_pow, Sp_eval, monP_eval]
    simp

theorem monP_append (v : Fin n → ℝ) (M1 M2 : Mon) :
    monP v (M1 ++ M2) = monP v M1 * monP v M2 := by simp [monP]

theorem trmP_mulT (v : Fin n → ℝ) (s t : TrmN) : trmP v (mulT s t) = trmP v s * trmP v t := by
  simp only [trmP, mulT, monP_append, pow_add, Nat.cast_mul, C_mul]
  ring

theorem polyPN_map_mulT (v : Fin n → ℝ) (s : TrmN) (L : List TrmN) :
    polyPN v (L.map (mulT s)) = trmP v s * polyPN v L := by
  induction L with
  | nil => simp [polyPN_nil]
  | cons t ts ih => rw [List.map_cons, polyPN_cons, polyPN_cons, ih, trmP_mulT]; ring

theorem polyPN_mulL (v : Fin n → ℝ) (L1 L2 : List TrmN) :
    polyPN v (mulL L1 L2) = polyPN v L1 * polyPN v L2 := by
  induction L1 with
  | nil => simp [mulL, polyPN_nil]
  | cons s ss ih =>
    have : mulL (s :: ss) L2 = L2.map (mulT s) ++ mulL ss L2 := by simp [mulL]
    rw [this, polyPN_append, polyPN_map_mulT, ih, polyPN_cons]; ring

theorem polyPN_powL (v : Fin n → ℝ) (L : List TrmN) (k : ℕ) :
    polyPN v (powL L k) = polyPN v L ^ k := by
  induction k with
  | zero => simp [powL, polyPN, monP]
  | succ k ih => rw [powL, polyPN_mulL, ih, pow_succ]; ring

theorem trmP_hom (v : Fin n → ℝ) (t : TrmN) : (trmP v t).IsHomogeneous (tdeg t) := by
  have := (isHomogeneous_C (Fin n) (t.1 : ℝ)).mul (monP_hom v t.2.1 t.2.2)
  rwa [zero_add] at this

theorem polyPN_hom (v : Fin n → ℝ) (L : List TrmN) (D : ℕ) (h : ∀ t ∈ L, tdeg t = D) :
    (polyPN v L).IsHomogeneous D := by
  induction L with
  | nil => simpa [polyPN_nil] using isHomogeneous_zero (Fin n) ℝ D
  | cons t ts ih =>
    rw [polyPN_cons]
    refine IsHomogeneous.add ?_ (ih fun s hs => h s (List.mem_cons_of_mem _ hs))
    have := trmP_hom v t
    rwa [h t List.mem_cons_self] at this

theorem polyPN_dvEs (v : Fin n → ℝ) (f g c : ℕ) (L : List TrmN)
    (h : ∀ t ∈ L, t.2.2.length + mdeg t.2.2 ≤ f ∧ t.2.1 + mdeg t.2.2 ≤ g) :
    gE ((dvD v)^[c] (polyPN v L)) = dvEsL (pw v) f g c L := by
  rw [← gD_apply, polyPN,
    lin_list_sum (gD v c) L (fun t => (t.1 : ℝ)) (fun t => Sp v 1 1 ^ t.2.1 * monP v t.2.2),
    dvEsL]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [gD_apply, dvEs_correct v f g c t.2.1 t.2.2 (h t ht).1 (h t ht).2]

/-! ## The split by degree -/

theorem polyPN_split (v : Fin n → ℝ) (D : ℕ) (L : List TrmN)
    (h : ∀ t ∈ L, tdeg t ≤ 2 * D ∧ Even (tdeg t)) :
    polyPN v L = ∑ q ∈ Finset.range (D + 1), polyPN v (L.filter fun t => tdeg t = 2 * q) := by
  induction L with
  | nil => simp [polyPN_nil]
  | cons t ts ih =>
    obtain ⟨hle, r, hr⟩ := h t List.mem_cons_self
    have hr' : tdeg t = 2 * r := by omega
    have key : ∀ q ∈ Finset.range (D + 1),
        polyPN v ((t :: ts).filter fun t => tdeg t = 2 * q) =
          (if q = r then trmP v t else 0) + polyPN v (ts.filter fun t => tdeg t = 2 * q) := by
      intro q _
      by_cases hq : q = r
      · subst hq
        rw [List.filter_cons_of_pos (by simpa using hr'), polyPN_cons, if_pos rfl]
      · rw [List.filter_cons_of_neg (by simp; omega), if_neg hq, zero_add]
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib,
      ← ih fun s hs => h s (List.mem_cons_of_mem _ hs), polyPN_cons,
      Finset.sum_ite_eq' (Finset.range (D + 1)) r, if_pos (Finset.mem_range.mpr (by omega))]

/-- The surrogate expectation as a linear functional. -/
noncomputable def sE (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) :
    MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun P := ∫ x, eval x P ∂surrRK n K t v
  map_add' P Q := by
    simp only [eval_add]
    exact integral_add (surr_int69 hn K t ht v (MvPolynomial.continuous_eval P))
      (surr_int69 hn K t ht v (MvPolynomial.continuous_eval Q))
  map_smul' c P := by
    simp only [smul_eq_C_mul, eval_mul, eval_C, smul_eq_mul]
    exact integral_const_mul _ _

theorem sE_apply (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ)
    (P : MvPolynomial (Fin n) ℝ) : sE hn K t ht v P = ∫ x, eval x P ∂surrRK n K t v := rfl

theorem IL74_odd (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) (f g D : ℕ) (L : List TrmN)
    (h : ∀ t ∈ L, Odd (tdeg t)) : IL74 n K t v f g D L = 0 := by
  have hf : ∀ q : ℕ, (L.filter fun t => tdeg t = 2 * q) = [] := by
    intro q
    rw [List.filter_eq_nil_iff]
    intro s hs
    obtain ⟨r, hr⟩ := h s hs
    simp; omega
  unfold IL74 ILF
  simp [hf, dvEsL]

theorem polyPN_odd (v : Fin n → ℝ) (L : List TrmN) (h : ∀ t ∈ L, Odd (tdeg t))
    (x : Fin n → ℝ) : eval (-x) (polyPN v L) = -eval x (polyPN v L) := by
  induction L with
  | nil => simp [polyPN_nil]
  | cons t ts ih =>
    rw [polyPN_cons, eval_add, eval_add, ih fun s hs => h s (List.mem_cons_of_mem _ hs)]
    have h1 := BstLean.Part71.sh_eval_smul (trmP v t) (tdeg t) (trmP_hom v t) (-1) x
    rw [(h t List.mem_cons_self).neg_one_pow, neg_one_smul] at h1
    rw [h1]; ring

/-- **The generic engine theorem.** For a list `L` of terms of even degree `≤ 2D` (or all of odd
degree), the surrogate expectation of its polynomial is the engine output `IL74`. -/
theorem surrL74 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (f g D : ℕ) (L : List TrmN)
    (h : ∀ t ∈ L, tdeg t ≤ 2 * D ∧ t.2.2.length + mdeg t.2.2 ≤ f ∧ t.2.1 + mdeg t.2.2 ≤ g)
    (hpar : (∀ t ∈ L, Even (tdeg t)) ∨ (∀ t ∈ L, Odd (tdeg t))) :
    ∫ x, eval x (polyPN v L) ∂surrRK n K t v = IL74 n K t v f g D L := by
  rcases hpar with hev | hodd
  · rw [← sE_apply hn K t ht v, polyPN_split v D L fun s hs => ⟨(h s hs).1, hev s hs⟩, map_sum]
    unfold IL74 ILF
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q _
    rw [sE_apply, surr74 hn K t ht v hv _ q
      (polyPN_hom v _ (2 * q) fun s hs => by simpa using (List.mem_filter.mp hs).2)]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    rw [polyPN_dvEs v f g (2 * c) _ fun s hs => (h s (List.mem_filter.mp hs).1).2]
  · rw [IL74_odd n K t v f g D L hodd]
    exact antipodal_odd69 hn K t ht v (MvPolynomial.continuous_eval _) (polyPN_odd v L hodd)

theorem surrL74_odd (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ)
    (f g D : ℕ) (L : List TrmN) (hodd : ∀ t ∈ L, Odd (tdeg t)) :
    ∫ x, eval x (polyPN v L) ∂surrRK n K t v = IL74 n K t v f g D L := by
  rw [IL74_odd n K t v f g D L hodd]
  exact antipodal_odd69 hn K t ht v (MvPolynomial.continuous_eval _) (polyPN_odd v L hodd)

/-! ## The lists at `(3, 3)` -/

/-- The side conditions of `surrL74` at the fuel `(12, 8)` and `D = 4`, even case (Boolean). -/
def okEb (L : List TrmN) : Bool :=
  L.all fun t => decide (tdeg t ≤ 8) && decide (t.2.2.length + mdeg t.2.2 ≤ 12) &&
    decide (t.2.1 + mdeg t.2.2 ≤ 8) && decide (tdeg t % 2 = 0)

/-- All terms have odd degree (Boolean). -/
def oddLb (L : List TrmN) : Bool := L.all fun t => decide (tdeg t % 2 = 1)

/-- Even case with the side conditions, or odd case. -/
def okb (L : List TrmN) : Bool := okEb L || oddLb L

theorem int_ok (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (L : List TrmN) (h : okb L = true) :
    ∫ x, eval x (polyPN v L) ∂surrRK n K t v = I33 (pw v) (W74 n K t) (Z69 n K t 0) L := by
  unfold okb at h
  rcases Bool.or_eq_true _ _ |>.mp h with h | h
  · have h' : ∀ s ∈ L, ((tdeg s ≤ 8 ∧ s.2.2.length + mdeg s.2.2 ≤ 12) ∧
        s.2.1 + mdeg s.2.2 ≤ 8) ∧ tdeg s % 2 = 0 := by
      simpa [okEb, List.all_eq_true] using h
    exact surrL74 hn K t ht v hv 12 8 4 L
      (fun s hs => ⟨(h' s hs).1.1.1, (h' s hs).1.1.2, (h' s hs).1.2⟩)
      (Or.inl fun s hs => Nat.even_iff.mpr (h' s hs).2)
  · have h' : ∀ s ∈ L, tdeg s % 2 = 1 := by simpa [oddLb, List.all_eq_true] using h
    exact surrL74_odd hn K t ht v 12 8 4 L fun s hs => Nat.odd_iff.mpr (h' s hs)

/-- The check for the words `c₁ + c₂ + c₃ ≤ 3`. -/
def chkWord : Bool :=
  (List.range 4).all fun c1 => (List.range 4).all fun c2 => (List.range 4).all fun c3 =>
    !decide (c1 + c2 + c3 ≤ 3) || okb (wordL c1 c2 c3)

/-- The check for the `τ` lists, words `c₁ + c₂ + c₃ ≤ 1`. -/
def chkTau : Bool :=
  [X4L, X6L, powL sL33 2, powL N2L 2, powL N3L 2].all fun X =>
    (List.range 2).all fun c1 => (List.range 2).all fun c2 => (List.range 2).all fun c3 =>
      !decide (c1 + c2 + c3 ≤ 1) || okb (mulL X (wordL c1 c2 c3))

theorem chkWord_true : chkWord = true := by decide

theorem chkTau_true : chkTau = true := by decide

theorem ok_word (c1 c2 c3 : ℕ) (hc : c1 + c2 + c3 ≤ 3) : okb (wordL c1 c2 c3) = true := by
  have h := chkWord_true
  simp only [chkWord, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  rcases h c1 (by omega) c2 (by omega) c3 (by omega) with h | h
  · exact absurd hc h
  · exact h

theorem ok_tau (X : List TrmN) (hX : X ∈ [X4L, X6L, powL sL33 2, powL N2L 2, powL N3L 2])
    (c1 c2 c3 : ℕ) (hc : c1 + c2 + c3 ≤ 1) : okb (mulL X (wordL c1 c2 c3)) = true := by
  have h := chkTau_true
  simp only [chkTau, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  rcases h X hX c1 (by omega) c2 (by omega) c3 (by omega) with h | h
  · exact absurd hc h
  · exact h

/-! ## Evaluation of the lists -/

theorem ev_s (v x : Fin n → ℝ) : eval x (polyPN v sL33) = sv69 v x := by
  simp [polyPN_eval, sL33, sv69]

theorem ev_N2 (v x : Fin n → ℝ) : eval x (polyPN v N2L) = sv69 v x ^ 2 + wv69 v x := by
  simp [polyPN_eval, N2L, sv69, wv69]

theorem ev_N3 (v x : Fin n → ℝ) :
    eval x (polyPN v N3L) = sv69 v x ^ 3 + 3 * sv69 v x * wv69 v x + 2 * cv74 v x := by
  simp [polyPN_eval, N3L, sv69, wv69, cv74]
  ring

theorem ev_X4 (v x : Fin n → ℝ) : eval x (polyPN v X4L) = x4_69 x := by
  simp [polyPN_eval, X4L, x4_69]

theorem ev_X6 (v x : Fin n → ℝ) : eval x (polyPN v X6L) = x6_74 x := by
  simp [polyPN_eval, X6L, x6_74]

theorem ev_word (v x : Fin n → ℝ) (c1 c2 c3 : ℕ) :
    eval x (polyPN v (wordL c1 c2 c3)) = sv69 v x ^ c1 * (sv69 v x ^ 2 + wv69 v x) ^ c2 *
      (sv69 v x ^ 3 + 3 * sv69 v x * wv69 v x + 2 * cv74 v x) ^ c3 := by
  unfold wordL
  simp only [polyPN_mulL, polyPN_powL, eval_mul, eval_pow, ev_s, ev_N2, ev_N3]
  ring

/-! ## The two integrals -/

theorem int_mom33 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (c1 c2 c3 : ℕ) (hc : c1 + c2 + c3 ≤ 3) :
    ∫ x, integrand33_74 v 0 c1 c2 c3 x ∂surrRK n K t v =
      mom33F (pw v) (W74 n K t) (Z69 n K t 0) c1 c2 c3 := by
  have hpt : ∀ x : Fin n → ℝ, integrand33_74 v 0 c1 c2 c3 x =
      eval x (polyPN v (wordL c1 c2 c3)) / den33 (pw v) c2 c3 := by
    intro x
    rw [ev_word]
    unfold integrand33_74 beta2_74 beta3_74 den33
    rw [div_pow, div_pow]
    ring
  simp only [hpt]
  rw [integral_div, int_ok hn K t ht v hv _
    (ok_word c1 c2 c3 hc)]
  rfl

theorem int_tau33 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (c1 c2 c3 : ℕ) (hc : c1 + c2 + c3 ≤ 1) :
    ∫ x, integrand33_74 v 1 c1 c2 c3 x ∂surrRK n K t v =
      tau33F (pw v) (W74 n K t) (Z69 n K t 0) c1 c2 c3 := by
  set wL := wordL c1 c2 c3 with hwL
  set P : MvPolynomial (Fin n) ℝ :=
    (5 / 3 : ℝ) • polyPN v wL + polyPN v (mulL X4L wL) + (1 / 3 : ℝ) • polyPN v (mulL X6L wL) -
      polyPN v (mulL (powL sL33 2) wL) -
      (1 / (2 * (1 + pw v 4)) : ℝ) • polyPN v (mulL (powL N2L 2) wL) -
      (1 / (6 * (1 + 3 * pw v 4 + 2 * pw v 6)) : ℝ) • polyPN v (mulL (powL N3L 2) wL) with hP
  have hpt : ∀ x : Fin n → ℝ, integrand33_74 v 1 c1 c2 c3 x =
      eval x P / den33 (pw v) c2 c3 := by
    intro x
    simp only [hP, eval_sub, eval_add, smul_eval, polyPN_mulL, polyPN_powL,
      eval_mul, eval_pow, ev_s, ev_N2, ev_N3, ev_X4, ev_X6, hwL, ev_word]
    unfold integrand33_74 tau33_74 beta2_74 beta3_74 den33
    have h2 : (1 + pw v 4) ≠ 0 := by have := pw4_nonneg74 v; positivity
    have h3 : (1 + 3 * pw v 4 + 2 * pw v 6) ≠ 0 := by
      have := pw4_nonneg74 v; have := pw6_nonneg74 v; positivity
    rw [div_pow, div_pow]
    field_simp
  simp only [hpt]
  rw [integral_div, ← sE_apply hn K t ht v]
  have hw := ok_word c1 c2 c3 (by omega : c1 + c2 + c3 ≤ 3)
  have ht' := fun X hX => ok_tau X hX c1 c2 c3 hc
  simp only [hP, map_sub, map_add, map_smul, smul_eq_mul, sE_apply]
  rw [int_ok hn K t ht v hv _ hw,
    int_ok hn K t ht v hv _ (ht' X4L (by simp)),
    int_ok hn K t ht v hv _ (ht' X6L (by simp)),
    int_ok hn K t ht v hv _ (ht' (powL sL33 2) (by simp)),
    int_ok hn K t ht v hv _ (ht' (powL N2L 2) (by simp)),
    int_ok hn K t ht v hv _ (ht' (powL N3L 2) (by simp))]
  unfold tau33F
  rw [← hwL]
  ring

/-! ## The weights -/

theorem core33 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (i l c1 c2 c3 : ℕ) (hi : i ≤ 3) (hl : 2 * l ≤ i) (hc : c1 + c2 + c3 ≤ i - 2 * l) :
    (if l = 0 then mom33F (pw v) (W74 n K t) (Z69 n K t 0) c1 c2 c3
      else if l = 1 then
        (if i = 2 then 1 else 3) *
          (1 / ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) / 6)) *
          tau33F (pw v) (W74 n K t) (Z69 n K t 0) c1 c2 c3
      else 0) =
      wickC i l * (1 / BstLean.Part36.DD n 3) ^ l *
        ∫ x, integrand33_74 v l c1 c2 c3 x ∂surrRK n K t v := by
  have hl01 : l = 0 ∨ l = 1 := by omega
  rcases hl01 with rfl | rfl
  · rw [if_pos rfl, wickC_i0_74, pow_zero, one_mul, one_mul,
      int_mom33 hn K t ht v hv c1 c2 c3 (by omega)]
  · rw [if_neg (by norm_num), if_pos rfl, pow_one, DD3_74,
      int_tau33 hn K t ht v hv c1 c2 c3 (by omega)]
    have hi23 : i = 2 ∨ i = 3 := by omega
    rcases hi23 with rfl | rfl
    · rw [if_pos rfl, wickC_21_74]
    · rw [if_neg (by norm_num), wickC_31_74]

/-- **The weights at `(3, 3)`.** At every key `(i, l, j⃗)` with `2l ≤ i` (the keys that `pg`
reads), the engine weight `w33` is the weight of the surrogate. -/
theorem weights33_74 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (κ : KeyRK 3 3) (hκ : 2 * (κ.1.2 : ℕ) ≤ (κ.1.1 : ℕ)) :
    w33 n K t v κ = wRK (surrRK n K t v) 3 v κ := by
  rw [wRK33_74 hn K t ht v hv κ]
  have hsum := cnt_sum74 κ
  have hi : (κ.1.1 : ℕ) ≤ 3 := by have := κ.1.1.isLt; omega
  exact core33 hn K t ht v hv _ _ _ _ _ hi hκ (by omega)

end BstLean.Part74

#print axioms BstLean.Part74.surrL74
#print axioms BstLean.Part74.weights33_74
