import BstLean.Part74GenDefs
import BstLean.Part74K33
import BstLean.Part69Prog

/-!
# Part 74: the constant-size stage of the `(3, 3)` moment program, built from the evaluators

The expression builders `exEG`, `exEGs`, `exdvEs`, `exdvEsL`, `exILF` mirror the evaluators `EG`,
`EGs`, `dvEs`, `dvEsL`, `ILF` as `Ex69p V33` trees with the constants `0`, `1` only.
`hp33Y`: a program of cost `B33` for `y ↦ w33Y y`. `w33Y_inp`: `w33Y (inp33 n K t v) = w33 n K t v`.
-/

namespace BstLean.Part74

open BstLean.Cost BstLean.Part56 BstLean.Part56.MomProg
open BstLean.Part69
open BstLean.Part69.Ex69p

/-- Expressions over the inputs of the constant-size stage. -/
abbrev E33 := Ex69p V33

/-- A natural number, as `0 + 1 + ⋯ + 1`. -/
def natE : ℕ → E33
  | 0 => 0
  | k + 1 => natE k + 1

@[simp] theorem natE_eval (y : V33 → ℝ) (k : ℕ) : (natE k).eval y = k := by
  induction k with
  | zero => simp [natE]
  | succ k ih => simp [natE, ih]

/-- The power sum `p_a`. -/
def pv (a : ℕ) : E33 := if h : a < 17 then var (Sum.inl ⟨a, h⟩) else 0

@[simp] theorem pv_eval (y : V33 → ℝ) (a : ℕ) : (pv a).eval y = pOf y a := by
  unfold pv pOf; split_ifs <;> simp

/-- The table sum `W_{c,q}`. -/
def wv (c q : ℕ) : E33 :=
  if h : c < 5 ∧ q < 5 then var (Sum.inr (Sum.inl (⟨c, h.1⟩, ⟨q, h.2⟩))) else 0

@[simp] theorem wv_eval (y : V33 → ℝ) (c q : ℕ) : (wv c q).eval y = WOf y c q := by
  unfold wv WOf; split_ifs <;> simp

/-- The sum of a list of expressions. -/
def sumE : List E33 → E33
  | [] => 0
  | e :: es => e + sumE es

@[simp] theorem sumE_eval (y : V33 → ℝ) (L : List E33) :
    (sumE L).eval y = (L.map fun e => e.eval y).sum := by
  induction L with
  | nil => simp [sumE]
  | cons e es ih => simp [sumE, ih]

/-- A power of an expression. -/
def powEx (e : E33) : ℕ → E33
  | 0 => 1
  | k + 1 => e * powEx e k

@[simp] theorem powEx_eval (y : V33 → ℝ) (e : E33) (k : ℕ) :
    (powEx e k).eval y = e.eval y ^ k := by
  induction k with
  | zero => simp [powEx]
  | succ k ih => simp [powEx, ih, pow_succ, mul_comm]

/-- A factorial. -/
def facE : ℕ → E33
  | 0 => 1
  | k + 1 => natE (k + 1) * facE k

@[simp] theorem facE_eval (y : V33 → ℝ) (k : ℕ) : (facE k).eval y = (k.factorial : ℝ) := by
  induction k with
  | zero => simp [facE]
  | succ k ih => simp [facE, ih, Nat.factorial_succ]

/-- Mirror of `EG`. -/
def exEG : ℕ → Mon → E33
  | _, [] => 1
  | 0, _ :: _ => 0
  | f + 1, (a, 0) :: M => pv a * exEG f M
  | f + 1, (a, 1) :: M => sumE ((pstep a 0 M).map fun y => natE y.1 * exEG f y.2)
  | f + 1, (a, b + 2) :: M =>
      natE (b + 1) * exEG f ((a, b) :: M) +
        sumE ((pstep a (b + 1) M).map fun y => natE y.1 * exEG f y.2)

theorem exEG_eval (y : V33 → ℝ) (f : ℕ) (M : Mon) :
    (exEG f M).eval y = EG (pOf y) f M := by
  induction f generalizing M with
  | zero => cases M <;> simp [exEG, EG]
  | succ f ih =>
    match M with
    | [] => simp [exEG, EG]
    | (a, 0) :: M => simp [exEG, EG, ih]
    | (a, 1) :: M => simp [exEG, EG, ih, Function.comp_def]
    | (a, b + 2) :: M => simp [exEG, EG, ih, Function.comp_def]

/-- Mirror of `EGs`. -/
def exEGs (f : ℕ) : ℕ → ℕ → Mon → E33
  | _, 0, M => exEG f M
  | 0, _ + 1, _ => 0
  | g + 1, 1, M => sumE ((dstep M).map fun y => natE y.1 * exEGs f g 0 y.2)
  | g + 1, e + 2, M =>
      natE (e + 1) * pv 2 * exEGs f g e M +
        sumE ((dstep M).map fun y => natE y.1 * exEGs f g (e + 1) y.2)

theorem exEGs_eval (y : V33 → ℝ) (f g e : ℕ) (M : Mon) :
    (exEGs f g e M).eval y = EGs (pOf y) f g e M := by
  induction g generalizing e M with
  | zero => cases e <;> simp [exEGs, EGs, exEG_eval]
  | succ g ih =>
    match e with
    | 0 => simp [exEGs, EGs, exEG_eval]
    | 1 => simp [exEGs, EGs, exEG_eval, Function.comp_def]
    | e + 2 => simp [exEGs, EGs, ih, Function.comp_def]

/-- Mirror of `dvEs`. -/
def exdvEs (f g : ℕ) : ℕ → ℕ → Mon → E33
  | 0, e, M => exEGs f g e M
  | c + 1, 0, M => sumE ((dstep M).map fun y => natE y.1 * exdvEs f g c 0 y.2)
  | c + 1, e + 1, M =>
      natE (e + 1) * pv 2 * exdvEs f g c e M +
        sumE ((dstep M).map fun y => natE y.1 * exdvEs f g c (e + 1) y.2)

theorem exdvEs_eval (y : V33 → ℝ) (f g c e : ℕ) (M : Mon) :
    (exdvEs f g c e M).eval y = dvEs (pOf y) f g c e M := by
  induction c generalizing e M with
  | zero => simp [exdvEs, dvEs, exEGs_eval]
  | succ c ih =>
    match e with
    | 0 => simp [exdvEs, dvEs, ih, Function.comp_def]
    | e + 1 => simp [exdvEs, dvEs, ih, Function.comp_def]

/-- Mirror of `dvEsL`. -/
def exdvEsL (f g c : ℕ) (L : List TrmN) : E33 :=
  sumE (L.map fun t => natE t.1 * exdvEs f g c t.2.1 t.2.2)

theorem exdvEsL_eval (y : V33 → ℝ) (f g c : ℕ) (L : List TrmN) :
    (exdvEsL f g c L).eval y = dvEsL (pOf y) f g c L := by
  simp [exdvEsL, dvEsL, exdvEs_eval, Function.comp_def]

theorem list_range_sum (f : ℕ → ℝ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- Mirror of `ILF`. -/
def exILF (f g D : ℕ) (L : List TrmN) : E33 :=
  sumE ((List.range (D + 1)).map fun q => sumE ((List.range (q + 1)).map fun c =>
    powEx (1 + 1) c / facE (2 * c) *
      exdvEsL f g (2 * c) (L.filter fun t => tdeg t = 2 * q) * wv c q)) /
    var (Sum.inr (Sum.inr ()))

theorem exILF_eval (y : V33 → ℝ) (f g D : ℕ) (L : List TrmN) :
    (exILF f g D L).eval y = ILF (pOf y) (WOf y) (y (Sum.inr (Sum.inr ()))) f g D L := by
  unfold exILF ILF
  simp only [eval_div, sumE_eval, List.map_map, Function.comp_def, eval_var, eval_mul,
    powEx_eval, facE_eval, exdvEsL_eval, wv_eval, eval_add, eval_one, list_range_sum]
  norm_num

/-! ## The weights at `(3, 3)` -/

/-- Mirror of `I33`. -/
def exI33 (L : List TrmN) : E33 := exILF 12 8 4 L

/-- Mirror of `den33`. -/
def exDen (c2 c3 : ℕ) : E33 :=
  powEx (1 + pv 4) c2 * powEx (1 + natE 3 * pv 4 + natE 2 * pv 6) c3

/-- Mirror of `mom33F`. -/
def exMom (c1 c2 c3 : ℕ) : E33 := exI33 (wordL c1 c2 c3) / exDen c2 c3

/-- Mirror of `tau33F`. -/
def exTau (c1 c2 c3 : ℕ) : E33 :=
  (natE 5 / natE 3 * exI33 (wordL c1 c2 c3) + exI33 (mulL X4L (wordL c1 c2 c3)) +
    exI33 (mulL X6L (wordL c1 c2 c3)) / natE 3 -
    exI33 (mulL (powL sL33 2) (wordL c1 c2 c3)) -
    exI33 (mulL (powL N2L 2) (wordL c1 c2 c3)) / (natE 2 * (1 + pv 4)) -
    exI33 (mulL (powL N3L 2) (wordL c1 c2 c3)) /
      (natE 6 * (1 + natE 3 * pv 4 + natE 2 * pv 6))) / exDen c2 c3

theorem exMom_eval (y : V33 → ℝ) (c1 c2 c3 : ℕ) :
    (exMom c1 c2 c3).eval y = mom33F (pOf y) (WOf y) (y (Sum.inr (Sum.inr ()))) c1 c2 c3 := by
  simp [exMom, mom33F, exI33, exDen, den33, exILF_eval]

theorem exTau_eval (y : V33 → ℝ) (c1 c2 c3 : ℕ) :
    (exTau c1 c2 c3).eval y = tau33F (pOf y) (WOf y) (y (Sum.inr (Sum.inr ()))) c1 c2 c3 := by
  simp [exTau, tau33F, exI33, exDen, den33, exILF_eval]

/-- The key classes `(l, [i ≠ 2], c₁, c₂, c₃)`. -/
abbrev Cls33 := Fin 3 × Fin 2 × Fin 4 × Fin 4 × Fin 4

/-- `n = p_0`. -/
def nnE : E33 := var (Sum.inl 0)

/-- The expression of a key class. -/
def exCls (o : Cls33) : E33 :=
  if (o.1 : ℕ) = 0 then
    (if (o.2.2.1 : ℕ) + (o.2.2.2.1 : ℕ) + (o.2.2.2.2 : ℕ) ≤ 3 then
      exMom o.2.2.1 o.2.2.2.1 o.2.2.2.2 else 0)
  else if (o.1 : ℕ) = 1 then
    (if (o.2.2.1 : ℕ) + (o.2.2.2.1 : ℕ) + (o.2.2.2.2 : ℕ) ≤ 1 then
      (if (o.2.1 : ℕ) = 0 then 1 else natE 3) *
        (1 / (nnE * (nnE + 1) * (nnE + natE 2) * (nnE + natE 3) / natE 6)) *
        exTau o.2.2.1 o.2.2.2.1 o.2.2.2.2 else 0)
  else 0

/-- The class of a key. -/
def sel33 (κ : KeyRK 3 3) : Cls33 :=
  (⟨min (κ.1.2 : ℕ) 2, by omega⟩, if (κ.1.1 : ℕ) = 2 then 0 else 1,
    ⟨min (cnt69 κ 1) 3, by omega⟩, ⟨min (cnt69 κ 2) 3, by omega⟩, ⟨min (cnt69 κ 3) 3, by omega⟩)

theorem exCls_eval (y : V33 → ℝ) (κ : KeyRK 3 3) :
    (exCls (sel33 κ)).eval y = w33Y y κ := by
  have hs := cnt_sum74 κ
  have hi : (κ.1.1 : ℕ) ≤ 3 := by have := κ.1.1.2; omega
  unfold w33Y w33F
  by_cases h0 : (κ.1.2 : ℕ) = 0
  · have hc : cnt69 κ 1 + cnt69 κ 2 + cnt69 κ 3 ≤ 3 := by omega
    have e1 : min (cnt69 κ 1) 3 = cnt69 κ 1 := by omega
    have e2 : min (cnt69 κ 2) 3 = cnt69 κ 2 := by omega
    have e3 : min (cnt69 κ 3) 3 = cnt69 κ 3 := by omega
    simp [exCls, sel33, h0, e1, e2, e3, hc, exMom_eval]
  · by_cases h1 : (κ.1.2 : ℕ) = 1
    · have hc : cnt69 κ 1 + cnt69 κ 2 + cnt69 κ 3 ≤ 1 := by omega
      have e1 : min (cnt69 κ 1) 3 = cnt69 κ 1 := by omega
      have e2 : min (cnt69 κ 2) 3 = cnt69 κ 2 := by omega
      have e3 : min (cnt69 κ 3) 3 = cnt69 κ 3 := by omega
      by_cases h2 : (κ.1.1 : ℕ) = 2
      · simp [exCls, sel33, h1, h2, e1, e2, e3, hc, exTau_eval, nnE]
      · simp [exCls, sel33, h1, h2, e1, e2, e3, hc, exTau_eval, nnE]
    · have e0 : min (κ.1.2 : ℕ) 2 = 2 := by omega
      simp [exCls, sel33, h0, h1, e0]

/-- The cost of the constant-size stage. -/
def B33 : ℕ := ∑ o : Cls33, (exCls o).size

/-- **The constant-size stage**: a program with the constants `0`, `1` only, of cost `B33`, that
maps the input vector `y` to the weights `w33Y y`. -/
theorem hp33Y : HasProg (fun (y : V33 → ℝ) (κ : KeyRK 3 3) => w33Y y κ) B33 := by
  have h := hp_mapOut (hp_parS (f := fun (y : V33 → ℝ) (o : Cls33) => (exCls o).eval y)
    (fun o => (exCls o).size) (fun o => hp (exCls o))) sel33
  exact hp_congr h (fun y κ => exCls_eval y κ)

set_option maxRecDepth 100000 in
theorem B33_le : B33 ≤ 1200000 := by decide +kernel

/-! ## The clamp congruence: the evaluators read `p_a` only for `a ≤ max 2 (weight)` -/

/-- The weight `Σ (a + b)` of a monomial. -/
def wtM (M : Mon) : ℕ := (M.map fun ab => ab.1 + ab.2).sum

theorem wtM_cons (ab : ℕ × ℕ) (M : Mon) : wtM (ab :: M) = ab.1 + ab.2 + wtM M := by
  simp [wtM]

theorem pstep_wt (a b : ℕ) (M : Mon) : ∀ y ∈ pstep a b M, wtM y.2 ≤ a + b + wtM M := by
  induction M with
  | nil => simp [pstep]
  | cons x xs ih =>
    obtain ⟨a', b'⟩ := x
    cases b' with
    | zero =>
      intro y hy
      simp only [pstep, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      have := ih z hz
      simp only [wtM_cons] at *
      omega
    | succ b' =>
      intro y hy
      simp only [pstep, List.mem_cons, List.mem_map] at hy
      rcases hy with rfl | ⟨z, hz, rfl⟩
      · simp only [wtM_cons]; omega
      · have := ih z hz
        simp only [wtM_cons] at *
        omega

theorem dstep_wt (M : Mon) : ∀ y ∈ dstep M, wtM y.2 ≤ wtM M := by
  induction M with
  | nil => simp [dstep]
  | cons x xs ih =>
    obtain ⟨a', b'⟩ := x
    cases b' with
    | zero =>
      intro y hy
      simp only [dstep, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      have := ih z hz
      simp only [wtM_cons] at *
      omega
    | succ b' =>
      intro y hy
      simp only [dstep, List.mem_cons, List.mem_map] at hy
      rcases hy with rfl | ⟨z, hz, rfl⟩
      · simp only [wtM_cons]; omega
      · have := ih z hz
        simp only [wtM_cons] at *
        omega

section Congr

variable {R : Type} [CommRing R]

theorem map_sum_congr {α : Type} (L : List α) (F G : α → R) (h : ∀ y ∈ L, F y = G y) :
    (L.map F).sum = (L.map G).sum := by
  rw [List.map_congr_left h]

theorem EG_congr (p p' : ℕ → R) (B : ℕ) (hp : ∀ a ≤ B, p a = p' a) (f : ℕ) (M : Mon)
    (hM : wtM M ≤ B) : EG p f M = EG p' f M := by
  induction f generalizing M with
  | zero => cases M <;> simp [EG]
  | succ f ih =>
    match M with
    | [] => simp [EG]
    | (a, 0) :: M =>
      simp only [wtM_cons] at hM
      simp only [EG]
      rw [hp a (by omega), ih M (by omega)]
    | (a, 1) :: M =>
      simp only [wtM_cons] at hM
      simp only [EG]
      apply map_sum_congr
      intro y hy
      rw [ih y.2 (by have := pstep_wt a 0 M y hy; omega)]
    | (a, b + 2) :: M =>
      simp only [wtM_cons] at hM
      simp only [EG]
      rw [ih ((a, b) :: M) (by simp only [wtM_cons]; omega)]
      congr 1
      apply map_sum_congr
      intro y hy
      rw [ih y.2 (by have := pstep_wt a (b + 1) M y hy; omega)]

theorem EGs_congr (p p' : ℕ → R) (B : ℕ) (hB : 2 ≤ B) (hp : ∀ a ≤ B, p a = p' a) (f g e : ℕ)
    (M : Mon) (hM : wtM M ≤ B) : EGs p f g e M = EGs p' f g e M := by
  induction g generalizing e M with
  | zero => cases e <;> simp [EGs, EG_congr p p' B hp f M hM]
  | succ g ih =>
    match e with
    | 0 => simp [EGs, EG_congr p p' B hp f M hM]
    | 1 =>
      simp only [EGs]
      apply map_sum_congr
      intro y hy
      rw [EG_congr p p' B hp f y.2 (le_trans (dstep_wt M y hy) hM)]
    | e + 2 =>
      simp only [EGs]
      rw [hp 2 hB, ih e M hM]
      congr 1
      apply map_sum_congr
      intro y hy
      rw [ih (e + 1) y.2 (le_trans (dstep_wt M y hy) hM)]

theorem dvEs_congr (p p' : ℕ → R) (B : ℕ) (hB : 2 ≤ B) (hp : ∀ a ≤ B, p a = p' a) (f g c e : ℕ)
    (M : Mon) (hM : wtM M ≤ B) : dvEs p f g c e M = dvEs p' f g c e M := by
  induction c generalizing e M with
  | zero => simp [dvEs, EGs_congr p p' B hB hp f g e M hM]
  | succ c ih =>
    match e with
    | 0 =>
      simp only [dvEs]
      apply map_sum_congr
      intro y hy
      rw [ih 0 y.2 (le_trans (dstep_wt M y hy) hM)]
    | e + 1 =>
      simp only [dvEs]
      rw [hp 2 hB, ih e M hM]
      congr 1
      apply map_sum_congr
      intro y hy
      rw [ih (e + 1) y.2 (le_trans (dstep_wt M y hy) hM)]

theorem dvEsL_congr (p p' : ℕ → R) (B : ℕ) (hB : 2 ≤ B) (hp : ∀ a ≤ B, p a = p' a) (f g c : ℕ)
    (L : List TrmN) (hL : ∀ t ∈ L, wtM t.2.2 ≤ B) : dvEsL p f g c L = dvEsL p' f g c L := by
  unfold dvEsL
  apply map_sum_congr
  intro t ht
  rw [dvEs_congr p p' B hB hp f g c t.2.1 t.2.2 (hL t ht)]

end Congr

theorem ILF_congr (p p' : ℕ → ℝ) (W W' : ℕ → ℕ → ℝ) (Z0 : ℝ) (B : ℕ) (hB : 2 ≤ B)
    (hp : ∀ a ≤ B, p a = p' a) (f g D : ℕ) (hW : ∀ c q, c ≤ q → q ≤ D → W c q = W' c q)
    (L : List TrmN) (hL : ∀ t ∈ L, tdeg t ≤ 2 * D → wtM t.2.2 ≤ B) :
    ILF p W Z0 f g D L = ILF p' W' Z0 f g D L := by
  unfold ILF
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro c hc
  have hq' : q ≤ D := by have := Finset.mem_range.mp hq; omega
  have hc' : c ≤ q := by have := Finset.mem_range.mp hc; omega
  rw [hW c q hc' hq', dvEsL_congr p p' B hB hp f g (2 * c) _ (fun t ht => by
    have h1 := List.mem_filter.mp ht
    have h2 : tdeg t = 2 * q := by simpa using h1.2
    exact hL t h1.1 (by omega))]

/-- The weight check on a polynomial: every term of degree `≤ 8` has weight `≤ 16`. -/
def okL (L : List TrmN) : Bool := L.all fun t => decide (tdeg t ≤ 8 → wtM t.2.2 ≤ 16)

theorem okL_spec (L : List TrmN) (h : okL L = true) :
    ∀ t ∈ L, tdeg t ≤ 2 * 4 → wtM t.2.2 ≤ 16 := by
  intro t ht hd
  have := List.all_eq_true.mp h t ht
  simp only [decide_eq_true_eq] at this
  exact this (by omega)

theorem ok_wordX : ∀ c1 < 4, ∀ c2 < 4, ∀ c3 < 4, c1 + c2 + c3 ≤ 3 →
    okL (wordL c1 c2 c3) = true := by decide +kernel

theorem ok_tauX : ∀ c1 < 2, ∀ c2 < 2, ∀ c3 < 2, c1 + c2 + c3 ≤ 1 →
    (okL (wordL c1 c2 c3) && okL (mulL X4L (wordL c1 c2 c3)) &&
      okL (mulL X6L (wordL c1 c2 c3)) && okL (mulL (powL sL33 2) (wordL c1 c2 c3)) &&
      okL (mulL (powL N2L 2) (wordL c1 c2 c3)) &&
      okL (mulL (powL N3L 2) (wordL c1 c2 c3))) = true := by decide +kernel

theorem pOf_inp (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) (a : ℕ) (ha : a ≤ 16) :
    pOf (inp33 n K t v) a = pw v a := by
  simp [pOf, inp33, show a < 17 by omega]

theorem WOf_inp (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) (c q : ℕ) (hc : c ≤ q) (hq : q ≤ 4) :
    WOf (inp33 n K t v) c q = W74 n K t c q := by
  simp [WOf, inp33, show c < 5 by omega, show q < 5 by omega, hc]

theorem I33_inp (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) (L : List TrmN) (h : okL L = true) :
    I33 (pOf (inp33 n K t v)) (WOf (inp33 n K t v)) (Z69 n K t 0) L =
      I33 (pw v) (W74 n K t) (Z69 n K t 0) L :=
  ILF_congr _ _ _ _ _ 16 (by norm_num) (fun a ha => pOf_inp n K t v a ha) 12 8 4
    (fun c q hc hq => WOf_inp n K t v c q hc hq) L (okL_spec L h)

/-- **The input vector `inp33 n K t v` gives the weights `w33 n K t v`**, at every key. -/
theorem w33Y_inp (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) (κ : KeyRK 3 3) :
    w33Y (inp33 n K t v) κ = w33 n K t v κ := by
  have hs := cnt_sum74 κ
  have hi : (κ.1.1 : ℕ) ≤ 3 := by have := κ.1.1.2; omega
  have hz : inp33 n K t v (Sum.inr (Sum.inr ())) = Z69 n K t 0 := rfl
  have hn0 : inp33 n K t v (Sum.inl 0) = (n : ℝ) := by simp [inp33, pw]
  have h4 := pOf_inp n K t v 4 (by norm_num)
  have h6 := pOf_inp n K t v 6 (by norm_num)
  unfold w33Y w33 w33F
  rw [hz, hn0]
  by_cases h0 : (κ.1.2 : ℕ) = 0
  · rw [if_pos h0, if_pos h0]
    have hk := ok_wordX (cnt69 κ 1) (by omega) (cnt69 κ 2) (by omega) (cnt69 κ 3) (by omega)
      (by omega)
    unfold mom33F den33
    rw [I33_inp n K t v _ hk, h4, h6]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : (κ.1.2 : ℕ) = 1
    · rw [if_pos h1, if_pos h1]
      have hk := ok_tauX (cnt69 κ 1) (by omega) (cnt69 κ 2) (by omega) (cnt69 κ 3) (by omega)
        (by omega)
      simp only [Bool.and_eq_true] at hk
      obtain ⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩ := hk
      unfold tau33F den33
      rw [I33_inp n K t v _ k1, I33_inp n K t v _ k2, I33_inp n K t v _ k3,
        I33_inp n K t v _ k4, I33_inp n K t v _ k5, I33_inp n K t v _ k6, h4, h6]
    · rw [if_neg h1, if_neg h1]

/-- **The constant-size stage after the input stage**: for every program that computes the input
vector `inp33 n K t v`, composition with `hp33Y` gives the weights `w33 n K t v`. -/
theorem hp33_w (n K : ℕ) : HasProg (fun (y : V33 → ℝ) (κ : KeyRK 3 3) => w33Y y κ) B33 ∧
    ∀ (t : ℝ) (v : Fin n → ℝ) κ, w33Y (inp33 n K t v) κ = w33 n K t v κ :=
  ⟨hp33Y, fun t v κ => w33Y_inp n K t v κ⟩

end BstLean.Part74

#print axioms BstLean.Part74.hp33Y
#print axioms BstLean.Part74.w33Y_inp
#print axioms BstLean.Part74.B33_le
