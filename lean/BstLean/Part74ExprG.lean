import BstLean.Part74LineDefs
import BstLean.Part74Expr

/-!
# Part 74: the constant-size stage of the line-program moment program at a general `(d, k)`

Generic expression builders (`exEGG`, `exEGsG`, `exdvEsG`, `exdvEsLG`, `exILFG`) over any variable
type, then the expression `exWG κ` of the weight `wGenY y κ`.
* `hpGenY`: a program (constants `0`, `1` only) of a cost `B` that depends on `(d, k)` only, for
  `y ↦ wGenY y`.
* `wGenY_inp`: `wGenY (inpG d k n K t v) κ = wGen n K t v κ` at every key.
-/

namespace BstLean.Part74

open BstLean.Cost BstLean.Part56 BstLean.Part56.MomProg
open BstLean.Part69
open BstLean.Part69.Ex69p

section Builders

variable {α : Type}

/-- A natural number, as `0 + 1 + ⋯ + 1`. -/
def natEG : ℕ → Ex69p α
  | 0 => 0
  | k + 1 => natEG k + 1

@[simp] theorem natEG_eval (y : α → ℝ) (k : ℕ) : (natEG k : Ex69p α).eval y = k := by
  induction k with
  | zero => simp [natEG]
  | succ k ih => simp [natEG, ih]

/-- The sum of a list of expressions. -/
def sumEG : List (Ex69p α) → Ex69p α
  | [] => 0
  | e :: es => e + sumEG es

@[simp] theorem sumEG_eval (y : α → ℝ) (L : List (Ex69p α)) :
    (sumEG L).eval y = (L.map fun e => e.eval y).sum := by
  induction L with
  | nil => simp [sumEG]
  | cons e es ih => simp [sumEG, ih]

/-- The product of a list of expressions. -/
def prodEG : List (Ex69p α) → Ex69p α
  | [] => 1
  | e :: es => e * prodEG es

@[simp] theorem prodEG_eval (y : α → ℝ) (L : List (Ex69p α)) :
    (prodEG L).eval y = (L.map fun e => e.eval y).prod := by
  induction L with
  | nil => simp [prodEG]
  | cons e es ih => simp [prodEG, ih]

/-- A power of an expression. -/
def powEG (e : Ex69p α) : ℕ → Ex69p α
  | 0 => 1
  | k + 1 => e * powEG e k

@[simp] theorem powEG_eval (y : α → ℝ) (e : Ex69p α) (k : ℕ) :
    (powEG e k).eval y = e.eval y ^ k := by
  induction k with
  | zero => simp [powEG]
  | succ k ih => simp [powEG, ih, pow_succ, mul_comm]

/-- A factorial. -/
def facEG : ℕ → Ex69p α
  | 0 => 1
  | k + 1 => natEG (k + 1) * facEG k

@[simp] theorem facEG_eval (y : α → ℝ) (k : ℕ) :
    (facEG k : Ex69p α).eval y = (k.factorial : ℝ) := by
  induction k with
  | zero => simp [facEG]
  | succ k ih => simp [facEG, ih, Nat.factorial_succ]

variable (pv : ℕ → Ex69p α) (wv : ℕ → ℕ → Ex69p α) (z0 : Ex69p α)

/-- Mirror of `EG`. -/
def exEGG : ℕ → Mon → Ex69p α
  | _, [] => 1
  | 0, _ :: _ => 0
  | f + 1, (a, 0) :: M => pv a * exEGG f M
  | f + 1, (a, 1) :: M => sumEG ((pstep a 0 M).map fun y => natEG y.1 * exEGG f y.2)
  | f + 1, (a, b + 2) :: M =>
      natEG (b + 1) * exEGG f ((a, b) :: M) +
        sumEG ((pstep a (b + 1) M).map fun y => natEG y.1 * exEGG f y.2)

theorem exEGG_eval (y : α → ℝ) (f : ℕ) (M : Mon) :
    (exEGG pv f M).eval y = EG (fun a => (pv a).eval y) f M := by
  induction f generalizing M with
  | zero => cases M <;> simp [exEGG, EG]
  | succ f ih =>
    match M with
    | [] => simp [exEGG, EG]
    | (a, 0) :: M => simp [exEGG, EG, ih]
    | (a, 1) :: M => simp [exEGG, EG, ih, Function.comp_def]
    | (a, b + 2) :: M => simp [exEGG, EG, ih, Function.comp_def]

/-- Mirror of `EGs`. -/
def exEGsG (f : ℕ) : ℕ → ℕ → Mon → Ex69p α
  | _, 0, M => exEGG pv f M
  | 0, _ + 1, _ => 0
  | g + 1, 1, M => sumEG ((dstep M).map fun y => natEG y.1 * exEGsG f g 0 y.2)
  | g + 1, e + 2, M =>
      natEG (e + 1) * pv 2 * exEGsG f g e M +
        sumEG ((dstep M).map fun y => natEG y.1 * exEGsG f g (e + 1) y.2)

theorem exEGsG_eval (y : α → ℝ) (f g e : ℕ) (M : Mon) :
    (exEGsG pv f g e M).eval y = EGs (fun a => (pv a).eval y) f g e M := by
  induction g generalizing e M with
  | zero => cases e <;> simp [exEGsG, EGs, exEGG_eval]
  | succ g ih =>
    match e with
    | 0 => simp [exEGsG, EGs, exEGG_eval]
    | 1 => simp [exEGsG, EGs, exEGG_eval, Function.comp_def]
    | e + 2 => simp [exEGsG, EGs, ih, Function.comp_def]

/-- Mirror of `dvEs`. -/
def exdvEsG (f g : ℕ) : ℕ → ℕ → Mon → Ex69p α
  | 0, e, M => exEGsG pv f g e M
  | c + 1, 0, M => sumEG ((dstep M).map fun y => natEG y.1 * exdvEsG f g c 0 y.2)
  | c + 1, e + 1, M =>
      natEG (e + 1) * pv 2 * exdvEsG f g c e M +
        sumEG ((dstep M).map fun y => natEG y.1 * exdvEsG f g c (e + 1) y.2)

theorem exdvEsG_eval (y : α → ℝ) (f g c e : ℕ) (M : Mon) :
    (exdvEsG pv f g c e M).eval y = dvEs (fun a => (pv a).eval y) f g c e M := by
  induction c generalizing e M with
  | zero => simp [exdvEsG, dvEs, exEGsG_eval]
  | succ c ih =>
    match e with
    | 0 => simp [exdvEsG, dvEs, ih, Function.comp_def]
    | e + 1 => simp [exdvEsG, dvEs, ih, Function.comp_def]

/-- Mirror of `dvEsL`. -/
def exdvEsLG (f g c : ℕ) (L : List TrmN) : Ex69p α :=
  sumEG (L.map fun t => natEG t.1 * exdvEsG pv f g c t.2.1 t.2.2)

theorem exdvEsLG_eval (y : α → ℝ) (f g c : ℕ) (L : List TrmN) :
    (exdvEsLG pv f g c L).eval y = dvEsL (fun a => (pv a).eval y) f g c L := by
  simp [exdvEsLG, dvEsL, exdvEsG_eval, Function.comp_def]

/-- Mirror of `ILF`. -/
def exILFG (f g D : ℕ) (L : List TrmN) : Ex69p α :=
  sumEG ((List.range (D + 1)).map fun q => sumEG ((List.range (q + 1)).map fun c =>
    powEG (1 + 1) c / facEG (2 * c) *
      exdvEsLG pv f g (2 * c) (L.filter fun t => tdeg t = 2 * q) * wv c q)) / z0

theorem exILFG_eval (y : α → ℝ) (f g D : ℕ) (L : List TrmN) :
    (exILFG pv wv z0 f g D L).eval y =
      ILF (fun a => (pv a).eval y) (fun c q => (wv c q).eval y) (z0.eval y) f g D L := by
  unfold exILFG ILF
  simp only [eval_div, sumEG_eval, List.map_map, Function.comp_def, eval_mul,
    powEG_eval, facEG_eval, exdvEsLG_eval, eval_add, eval_one, list_range_sum]
  norm_num

end Builders

theorem list_range_prod (f : ℕ → ℝ) (m : ℕ) :
    ((List.range m).map f).prod = ∏ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.prod_range_succ, ih]

/-! ## The weights at `(d, k)` -/

section Gen

variable {d k : ℕ}

/-- The power sum `p_a`. -/
def pvG (d k a : ℕ) : Ex69p (VG d k) :=
  if h : a < 2 * d * k + 3 then var (Sum.inl ⟨a, h⟩) else 0

theorem pvG_eval (y : VG d k → ℝ) : (fun a => (pvG d k a).eval y) = pOfG y := by
  funext a
  unfold pvG pOfG; split_ifs <;> simp

/-- The table sum `W_{c,q}`. -/
def wvG (d k c q : ℕ) : Ex69p (VG d k) :=
  if h : c < degD d k + 1 ∧ q < degD d k + 1 then
    var (Sum.inr (Sum.inl (⟨c, h.1⟩, ⟨q, h.2⟩))) else 0

theorem wvG_eval (y : VG d k → ℝ) : (fun c q => (wvG d k c q).eval y) = WOfG y := by
  funext c q
  unfold wvG WOfG; split_ifs <;> simp

/-- `Z_0`. -/
def z0G (d k : ℕ) : Ex69p (VG d k) := var (Sum.inr (Sum.inr ()))

/-- `n = p_0`. -/
def nnG (d k : ℕ) : Ex69p (VG d k) := var (Sum.inl ⟨0, by omega⟩)

/-- Mirror of `kvvF`. -/
def exKvvG (d k j : ℕ) : Ex69p (VG d k) :=
  exdvEsLG (pvG d k) (fuelF d k) (fuelG d k) 0 (AL sigV j) / facEG j

theorem exKvvG_eval (y : VG d k → ℝ) (j : ℕ) :
    (exKvvG d k j).eval y = kvvF (pOfG y) d k j := by
  simp [exKvvG, kvvF, exdvEsLG_eval, pvG_eval]

/-- Mirror of `tauC`. -/
def exTauCG (d k : ℕ) : Fin d ⊕ Fin d → Ex69p (VG d k)
  | Sum.inl j => 1 / facEG ((j : ℕ) + 1)
  | Sum.inr j => (0 - 1) / (facEG ((j : ℕ) + 1) * facEG ((j : ℕ) + 1) * exKvvG d k ((j : ℕ) + 1))

theorem exTauCG_eval (y : VG d k → ℝ) (m : Fin d ⊕ Fin d) :
    (exTauCG d k m).eval y = tauC (pOfG y) d k m := by
  cases m with
  | inl j => simp [exTauCG, tauC]
  | inr j => simp [exTauCG, tauC, exKvvG_eval, sq]

/-- Mirror of `DDF` at `n = p_0`. -/
def exDDFG (d k : ℕ) : Ex69p (VG d k) :=
  nnG d k * prodEG ((List.range d).map fun i => nnG d k + (natEG i + 1)) / facEG d

theorem exDDFG_eval (y : VG d k → ℝ) :
    (exDDFG d k).eval y = DDF (y (Sum.inl ⟨0, by omega⟩)) d := by
  simp [exDDFG, DDF, nnG, Function.comp_def, list_range_prod]

/-- The expression of the weight of a key. -/
noncomputable def exWG (κ : KeyRK k d) : Ex69p (VG d k) :=
  facEG (κ.1.1 : ℕ) /
      (powEG (1 + 1) (κ.1.2 : ℕ) * facEG (κ.1.2 : ℕ) * facEG ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ))) *
    powEG (1 / exDDFG d k) (κ.1.2 : ℕ) *
    sumEG ((Finset.univ : Finset (Fin (κ.1.2 : ℕ) → Fin d ⊕ Fin d)).toList.map fun μ =>
      prodEG ((Finset.univ : Finset (Fin (κ.1.2 : ℕ))).toList.map fun a => exTauCG d k (μ a)) *
        exILFG (pvG d k) (wvG d k) (z0G d k) (fuelF d k) (fuelG d k) (degD d k)
          (mulL (prodL fun a => tauL d (μ a)) (prodL fun r => AL sigX (κ.2 r)))) /
    prodEG ((Finset.univ : Finset (Fin ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ)))).toList.map fun r =>
      facEG (κ.2 r : ℕ) * exKvvG d k (κ.2 r))

theorem exWG_eval (y : VG d k → ℝ) (κ : KeyRK k d) : (exWG κ).eval y = wGenY y κ := by
  unfold exWG wGenY wGenF wickC
  simp only [eval_div, eval_mul, facEG_eval, powEG_eval, eval_add, eval_one, sumEG_eval,
    prodEG_eval, List.map_map, Function.comp_def, exTauCG_eval, exILFG_eval, pvG_eval, wvG_eval,
    exKvvG_eval, exDDFG_eval, z0G, eval_var]
  norm_num

/-- **The constant-size stage at `(d, k)`**: a program with the constants `0`, `1` only, of a cost
that depends on `(d, k)` only, that maps the input vector `y` to the weights `wGenY y`. -/
theorem hpGenY (d k : ℕ) :
    ∃ B : ℕ, HasProg (fun (y : VG d k → ℝ) (κ : KeyRK k d) => wGenY y κ) B := by
  classical
  refine ⟨∑ κ : KeyRK k d, (exWG κ).size, ?_⟩
  have h := hp_parS (f := fun (y : VG d k → ℝ) (κ : KeyRK k d) => (exWG κ).eval y)
    (fun κ => (exWG κ).size) (fun κ => hp (exWG κ))
  exact hp_congr h (fun y κ => exWG_eval y κ)

end Gen

/-! ## The clamp congruence -/

/-- A property of terms that holds for `1` and is closed under products. -/
structure MulClosed (Q : TrmN → Prop) : Prop where
  one : Q (1, 0, [])
  mul : ∀ s t, Q s → Q t → Q (mulT s t)

theorem mulL_all {Q : TrmN → Prop} (hQ : MulClosed Q) (L1 L2 : List TrmN)
    (h1 : ∀ t ∈ L1, Q t) (h2 : ∀ t ∈ L2, Q t) : ∀ t ∈ mulL L1 L2, Q t := by
  intro t ht
  simp only [mulL, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨s, hs, u, hu, rfl⟩ := ht
  exact hQ.mul s u (h1 s hs) (h2 u hu)

theorem powL_all {Q : TrmN → Prop} (hQ : MulClosed Q) (L : List TrmN) (h : ∀ t ∈ L, Q t)
    (m : ℕ) : ∀ t ∈ powL L m, Q t := by
  induction m with
  | zero => intro t ht; simp only [powL, List.mem_singleton] at ht; subst ht; exact hQ.one
  | succ m ih => exact mulL_all hQ _ _ h ih

theorem foldr_all {Q : TrmN → Prop} (hQ : MulClosed Q) (Ls : List (List TrmN))
    (h : ∀ L ∈ Ls, ∀ t ∈ L, Q t) : ∀ t ∈ Ls.foldr mulL [(1, 0, [])], Q t := by
  induction Ls with
  | nil => intro t ht; simp only [List.foldr, List.mem_singleton] at ht; subst ht; exact hQ.one
  | cons L Ls ih =>
    exact mulL_all hQ _ _ (h L (by simp)) (ih fun L' hL' => h L' (by simp [hL']))

theorem prodL_all {Q : TrmN → Prop} (hQ : MulClosed Q) {m : ℕ} (Ls : Fin m → List TrmN)
    (h : ∀ r, ∀ t ∈ Ls r, Q t) : ∀ t ∈ prodL Ls, Q t := by
  unfold prodL
  apply foldr_all hQ
  intro L hL
  obtain ⟨r, rfl⟩ := (List.mem_ofFn' _ _).mp hL
  exact h r

theorem wtM_append (M1 M2 : Mon) : wtM (M1 ++ M2) = wtM M1 + wtM M2 := by
  simp [wtM]

theorem mdeg_append (M1 M2 : Mon) : mdeg (M1 ++ M2) = mdeg M1 + mdeg M2 := by
  simp [mdeg]

/-- The weight is at most twice the degree. -/
def QW (t : TrmN) : Prop := wtM t.2.2 ≤ 2 * mdeg t.2.2

theorem QW_closed : MulClosed QW where
  one := by simp [QW, wtM, mdeg]
  mul s t hs ht := by
    simp only [QW, mulT, wtM_append, mdeg_append] at *
    omega

theorem newtStep_QW (σ : ℕ → ℕ × ℕ) (hσ : ∀ b, (σ b).1 + (σ b).2 ≤ 2 * (σ b).2) (j : ℕ)
    (rest : List (List TrmN)) (h : ∀ L ∈ rest, ∀ t ∈ L, QW t) (m : ℕ) :
    ∀ t ∈ newtStep σ j m rest, QW t := by
  induction rest generalizing m with
  | nil => simp [newtStep]
  | cons Lm rest ih =>
    intro t ht
    simp only [newtStep, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨u, hu, rfl⟩ | ht
    · have := h Lm (by simp) u hu
      have h2 := hσ (m + 1)
      simp only [QW, wtM_cons, mdeg, List.map_cons, List.sum_cons] at *
      omega
    · exact ih (fun L hL => h L (by simp [hL])) (m + 1) t ht

theorem ALs_QW (σ : ℕ → ℕ × ℕ) (hσ : ∀ b, (σ b).1 + (σ b).2 ≤ 2 * (σ b).2) (j : ℕ) :
    ∀ L ∈ ALs σ j, ∀ t ∈ L, QW t := by
  induction j with
  | zero =>
    intro L hL t ht
    simp only [ALs, List.mem_singleton] at hL
    subst hL
    simp only [List.mem_singleton] at ht
    subst ht
    exact QW_closed.one
  | succ j ih =>
    intro L hL
    simp only [ALs, List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact newtStep_QW σ hσ j _ ih 0
    · exact ih L hL

theorem AL_mem (σ : ℕ → ℕ × ℕ) (j : ℕ) : AL σ j ∈ ALs σ j := by
  unfold AL
  cases j <;> simp [ALs]

theorem AL_QW (σ : ℕ → ℕ × ℕ) (hσ : ∀ b, (σ b).1 + (σ b).2 ≤ 2 * (σ b).2) (j : ℕ) :
    ∀ t ∈ AL σ j, QW t := ALs_QW σ hσ j _ (AL_mem σ j)

theorem sigX_QW (b : ℕ) : (sigX b).1 + (sigX b).2 ≤ 2 * (sigX b).2 := by simp [sigX]; omega
theorem sigXX_QW (b : ℕ) : (sigXX b).1 + (sigXX b).2 ≤ 2 * (sigXX b).2 := by simp [sigXX]; omega

/-- The weight of the terms of `AL σ j` is at most `2j` when `σ b` has weight at most `2b`. -/
theorem newtStep_wt (σ : ℕ → ℕ × ℕ) (hσ : ∀ b, (σ b).1 + (σ b).2 ≤ 2 * b) (j : ℕ)
    (rest : List (List TrmN)) (m : ℕ)
    (h : ∀ (i : ℕ) (L : List TrmN), rest[i]? = some L → ∀ t ∈ L, wtM t.2.2 + 2 * (m + i) ≤ 2 * j) :
    ∀ t ∈ newtStep σ j m rest, wtM t.2.2 ≤ 2 * (j + 1) := by
  induction rest generalizing m with
  | nil => simp [newtStep]
  | cons Lm rest ih =>
    intro t ht
    simp only [newtStep, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨u, hu, rfl⟩ | ht
    · have := h 0 Lm (by simp) u hu
      have h2 := hσ (m + 1)
      simp only [wtM_cons] at *
      omega
    · refine ih (m + 1) (fun i L hi u hu => ?_) t ht
      have := h (i + 1) L (by simpa using hi) u hu
      omega

theorem ALs_wt (σ : ℕ → ℕ × ℕ) (hσ : ∀ b, (σ b).1 + (σ b).2 ≤ 2 * b) (j : ℕ) :
    ∀ (i : ℕ) (L : List TrmN), (ALs σ j)[i]? = some L → ∀ t ∈ L, wtM t.2.2 + 2 * i ≤ 2 * j := by
  induction j with
  | zero =>
    intro i L hi t ht
    cases i with
    | zero =>
      simp only [ALs, List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [List.mem_singleton] at ht
      subst ht
      simp [wtM]
    | succ i => simp [ALs] at hi
  | succ j ih =>
    intro i L hi t ht
    cases i with
    | zero =>
      simp only [ALs, List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      have := newtStep_wt σ hσ j (ALs σ j) 0 (fun i L hi u hu => by
        have := ih i L hi u hu; omega) t ht
      omega
    | succ i =>
      simp only [ALs, List.getElem?_cons_succ] at hi
      have := ih i L hi t ht
      omega

theorem AL_wt (σ : ℕ → ℕ × ℕ) (hσ : ∀ b, (σ b).1 + (σ b).2 ≤ 2 * b) (j : ℕ) :
    ∀ t ∈ AL σ j, wtM t.2.2 ≤ 2 * j := by
  intro t ht
  have h0 : (ALs σ j)[0]? = some (AL σ j) := by
    unfold AL
    cases j <;> simp [ALs]
  have := ALs_wt σ hσ j 0 _ h0 t ht
  omega

theorem sigV_wt (b : ℕ) : (sigV b).1 + (sigV b).2 ≤ 2 * b := by simp [sigV]

section Inp

variable {d k : ℕ} {n : ℕ}

theorem pOfG_inp (K : ℕ) (t : ℝ) (v : Fin n → ℝ) (a : ℕ) (ha : a ≤ 2 * d * k + 2) :
    pOfG (inpG d k n K t v) a = pw v a := by
  simp [pOfG, inpG, show a < 2 * d * k + 3 by omega]

theorem WOfG_inp (K : ℕ) (t : ℝ) (v : Fin n → ℝ) (c q : ℕ) (hc : c ≤ q) (hq : q ≤ degD d k) :
    WOfG (inpG d k n K t v) c q = W74 n K t c q := by
  simp [WOfG, inpG, show c < degD d k + 1 by omega, show q < degD d k + 1 by omega, hc]

theorem kvvF_inp (K : ℕ) (t : ℝ) (v : Fin n → ℝ) (j : ℕ) (hj : j ≤ d) (hk : 1 ≤ k) :
    kvvF (pOfG (inpG d k n K t v)) d k j = kvvF (pw v) d k j := by
  unfold kvvF
  have hdk : d ≤ d * k := Nat.le_mul_of_pos_right d hk
  rw [dvEsL_congr _ (pw v) (2 * d * k + 2) (by omega) (fun a ha => pOfG_inp K t v a ha) _ _ _ _
    (fun u hu => by
      have := AL_wt sigV sigV_wt j u hu
      have : 2 * d * k = 2 * (d * k) := by ring
      omega)]

theorem tauC_inp (K : ℕ) (t : ℝ) (v : Fin n → ℝ) (hk : 1 ≤ k) (m : Fin d ⊕ Fin d) :
    tauC (pOfG (inpG d k n K t v)) d k m = tauC (pw v) d k m := by
  cases m with
  | inl j => rfl
  | inr j =>
    simp only [tauC]
    rw [kvvF_inp K t v _ (by have := j.2; omega) hk]

theorem ILF_inp (K : ℕ) (t : ℝ) (v : Fin n → ℝ) (L : List TrmN) (hL : ∀ u ∈ L, QW u) :
    ILF (pOfG (inpG d k n K t v)) (WOfG (inpG d k n K t v)) (Z69 n K t 0) (fuelF d k)
        (fuelG d k) (degD d k) L =
      ILF (pw v) (W74 n K t) (Z69 n K t 0) (fuelF d k) (fuelG d k) (degD d k) L :=
  ILF_congr _ _ _ _ _ (2 * d * k + 2) (by omega) (fun a ha => pOfG_inp K t v a ha) _ _ _
    (fun c q hc hq => WOfG_inp K t v c q hc hq) L (fun u hu hd => by
      have h1 : wtM u.2.2 ≤ 2 * mdeg u.2.2 := hL u hu
      have h2 : mdeg u.2.2 ≤ tdeg u := by unfold tdeg; omega
      have h3 : 2 * degD d k ≤ d * k + 1 := by unfold degD; omega
      have : 2 * d * k = 2 * (d * k) := by ring
      omega)

/-- **The input vector `inpG d k n K t v` gives the weights `wGen n K t v`**, at every key. -/
theorem wGenY_inp (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) (κ : KeyRK k d) :
    wGenY (inpG d k n K t v) κ = wGen n K t v κ := by
  have hz : inpG d k n K t v (Sum.inr (Sum.inr ())) = Z69 n K t 0 := rfl
  have hn0 : inpG d k n K t v (Sum.inl ⟨0, by omega⟩) = (n : ℝ) := by simp [inpG, pw]
  have hi : (κ.1.1 : ℕ) ≤ k := by have := κ.1.1.2; omega
  unfold wGenY wGen wGenF
  rw [hz, hn0]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro μ _
    congr 1
    · apply Finset.prod_congr rfl
      intro a _
      have hl : 1 ≤ (κ.1.2 : ℕ) := by have := a.2; omega
      have hl2 : (κ.1.2 : ℕ) ≤ k := by have := κ.1.2.2; omega
      exact tauC_inp K t v (by omega) (μ a)
    · apply ILF_inp
      apply mulL_all QW_closed
      · apply prodL_all QW_closed
        intro a
        cases μ a with
        | inl j => exact AL_QW sigXX sigXX_QW _
        | inr j => exact powL_all QW_closed _ (AL_QW sigX sigX_QW _) 2
      · apply prodL_all QW_closed
        intro r
        exact AL_QW sigX sigX_QW _
  · apply Finset.prod_congr rfl
    intro r _
    have hr : 1 ≤ (κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ) := by have := r.2; omega
    rw [kvvF_inp K t v _ (by have := (κ.2 r).2; omega) (by omega)]

end Inp

end BstLean.Part74

#print axioms BstLean.Part74.hpGenY
#print axioms BstLean.Part74.wGenY_inp
