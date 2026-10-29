import BstLean.Part282Kit
import BstLean.Part157Paper

/-!
# Part 282 (C2), one draw: the latitude, the node search, and the hit

Paper: `theorem7-01-statement-program.tex`, step 6. Lean: `Part157Prog.latitude`,
`Part157Paper.nodeIdx`, `Part157Paper.gridMix`, `Part157Prog.drawY`, `Part157Prog.hitFn`.

* `latProg k`: the latitude `s = a_x/√(a_x² + τ²ΣG²)`, `a_x = a + τZ`, from the inputs
  `a = |ĉ|`, `τ = τ₀`, `τ² `, `Z`, `G₁, …, G_k`. `latProg_eval`: its value is `latitude`.
  `latProg_cost`: `2k + 5` operations (`= 2n + 4` for `k = n − 1`).
* `bsearch`: a binary search with comparisons; `bsearch_spec` (its result), `bsearch_count`
  (at most `Nat.log 2 d + 1` comparisons for a range of length `d`).
  `selectNode`: one comparison `L < H` and then the binary search over the cell boundaries
  `L + gΔ`, `g = 1, …, J − 1`. `selectNode_eq`: its result is `nodeIdx J L H s`.
  `selectNode_count`: at most `Nat.log 2 J + 2` comparisons.
* `hitProg n m`: from the table values `f̃_g`, `ω̃_g`, the inputs `√e_b`, `t`, `c_A`, `η` and the
  weights of `F`: `λ̃ = f̃/√e_b`, `S̃ = (2/n)max(1/5, ω̃ − f̃²)`, `y = λ̃c_A + √S̃η`, `F(y)` and the
  hit indicator `relu(F(y) − t)/relu(F(y) − t)`. `hitProg_eval`; `hitProg_cost`
  (`3n + 11 + mlpCost n m 1`).
* `hitFn_eq_hitProg`: for the design `paperDesign n fT wT` (so for `statedDesign n`), the value
  of one draw `hitFn` is `hitProg` at the node `nodeIdx` of the latitude.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part157

noncomputable section

/-! ## The latitude -/

/-- The inputs of the latitude program: `![a, τ, τ², Z]` and `G`. -/
abbrev LatIn (k : ℕ) : Type := Fin 4 ⊕ Fin k

def latVal {k : ℕ} (a τ τ2 Z : ℝ) (G : Fin k → ℝ) : LatIn k → ℝ := Sum.elim ![a, τ, τ2, Z] G

/-- `Σ G_i²`: `2k − 1` operations. -/
def sqSumProg (k : ℕ) : RProg (LatIn k) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange k).map fun i => (Arg.inp (Sum.inr i), Arg.inp (Sum.inr i))))

theorem sqSumProg_eval {k : ℕ} (a τ τ2 Z : ℝ) (G : Fin k → ℝ) :
    (sqSumProg k).eval (latVal a τ τ2 Z G) () = normSq G := by
  rw [sqSumProg, RProg.eval_ofProg, eval_sumProd, List.map_map, normSq, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Arg.eval, latVal, pow_two]

theorem sqSumProg_cost (k : ℕ) : (sqSumProg k).cost = 2 * k - 1 := by
  rw [sqSumProg, RProg.cost_ofProg, cost_sumProd]
  simp

/-- `a_x = a + τZ`. -/
def axE (k : ℕ) : RExpr (LatIn k ⊕ Unit) :=
  RExpr.add (.inp (Sum.inl (Sum.inl 0))) (RExpr.mul (.inp (Sum.inl (Sum.inl 1))) (.inp (Sum.inl (Sum.inl 3))))

/-- `a_x/√(a_x·a_x + τ²·ΣG²)`. -/
def latE (k : ℕ) : RExpr (LatIn k ⊕ (Unit ⊕ Unit)) :=
  RExpr.div (.inp (Sum.inr (Sum.inr ())))
    (RExpr.sqrt (RExpr.add (RExpr.mul (.inp (Sum.inr (Sum.inr ()))) (.inp (Sum.inr (Sum.inr ()))))
      (RExpr.mul (.inp (Sum.inl (Sum.inl 2))) (.inp (Sum.inr (Sum.inl ()))))))

/-- **The latitude program.** -/
def latProg (k : ℕ) : RProg (LatIn k) Unit :=
  (RProg.ext (sqSumProg k) (axE k).prog).bind (latE k).prog

theorem latProg_eval {k : ℕ} (a τ Z : ℝ) (G : Fin k → ℝ) :
    (latProg k).eval (latVal a τ (τ ^ 2) Z G) () = latitude (n := k + 1) a τ (Z, G) := by
  rw [latProg, RProg.eval_bind, RExpr.eval_prog]
  simp only [latE, axE, RExpr.eval_div, RExpr.eval_sqrt, RExpr.eval_add, RExpr.eval_mul,
    RExpr.eval_inp, Sum.elim_inr, Sum.elim_inl, RProg.eval_ext_inl, RProg.eval_ext_inr,
    RExpr.eval_prog, sqSumProg_eval]
  simp only [latVal, Sum.elim_inl, latitude]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons]
  congr 1
  rw [pow_two (a + τ * Z)]
  rfl

theorem latProg_cost (k : ℕ) : (latProg k).cost = 2 * k - 1 + 7 := by
  simp [latProg, RProg.cost_bind, sqSumProg_cost, axE, latE]

/-! ## The node: a binary search with comparisons -/

open Classical in
/-- Binary search for the last `g ∈ [lo, hi]` with `p g` (or `lo`). The second component is the
number of comparisons (evaluations of `p`). -/
noncomputable def bsearch (p : ℕ → Prop) (lo hi : ℕ) : ℕ × ℕ :=
  if lo < hi then
    if p ((lo + hi + 1) / 2) then
      ((bsearch p ((lo + hi + 1) / 2) hi).1, (bsearch p ((lo + hi + 1) / 2) hi).2 + 1)
    else ((bsearch p lo ((lo + hi + 1) / 2 - 1)).1, (bsearch p lo ((lo + hi + 1) / 2 - 1)).2 + 1)
  else (lo, 0)
termination_by hi - lo
decreasing_by all_goals omega

/-- **The result of the binary search** for a predicate `p` that holds on an initial segment. -/
theorem bsearch_spec (p : ℕ → Prop) (hp : ∀ a b, a ≤ b → p b → p a) :
    ∀ d lo hi, hi - lo = d → lo ≤ hi →
      lo ≤ (bsearch p lo hi).1 ∧ (bsearch p lo hi).1 ≤ hi ∧
      ((bsearch p lo hi).1 = lo ∨ p (bsearch p lo hi).1) ∧
      ∀ g, (bsearch p lo hi).1 < g → g ≤ hi → ¬ p g := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro lo hi hd hle
    rw [bsearch]
    by_cases h : lo < hi
    · rw [if_pos h]
      by_cases hm : p ((lo + hi + 1) / 2)
      · rw [if_pos hm]
        obtain ⟨h1, h2, h3, h4⟩ := ih (hi - (lo + hi + 1) / 2) (by omega) _ hi rfl (by omega)
        refine ⟨by omega, h2, Or.inr ?_, h4⟩
        rcases h3 with h3 | h3
        · rw [h3]; exact hm
        · exact h3
      · rw [if_neg hm]
        obtain ⟨h1, h2, h3, h4⟩ :=
          ih ((lo + hi + 1) / 2 - 1 - lo) (by omega) lo _ rfl (by omega)
        refine ⟨h1, by omega, h3, fun g hg hgh => ?_⟩
        by_cases hg' : g ≤ (lo + hi + 1) / 2 - 1
        · exact h4 g hg hg'
        · exact fun hpg => hm (hp _ g (by omega) hpg)
    · rw [if_neg h]
      exact ⟨le_rfl, hle, Or.inl rfl, fun g hg hgh => by omega⟩

/-- **The number of comparisons of the binary search.** -/
theorem bsearch_count (p : ℕ → Prop) :
    ∀ d lo hi, hi - lo = d → (bsearch p lo hi).2 ≤ (if d = 0 then 0 else Nat.log 2 d + 1) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro lo hi hd
    rw [bsearch]
    by_cases h : lo < hi
    · have hd0 : d ≠ 0 := by omega
      rw [if_pos h]
      have key : ∀ d', d' ≤ d / 2 → (if d' = 0 then 0 else Nat.log 2 d' + 1) + 1 ≤
          Nat.log 2 d + 1 := by
        intro d' hd'
        by_cases h0 : d' = 0
        · rw [if_pos h0]; omega
        · rw [if_neg h0]
          have h2 : 2 ≤ d := by omega
          have hl := Nat.log_pos (by norm_num : 1 < 2) h2
          have hm : Nat.log 2 d' ≤ Nat.log 2 (d / 2) := Nat.log_mono_right hd'
          rw [Nat.log_div_base] at hm
          omega
      by_cases hm : p ((lo + hi + 1) / 2)
      · rw [if_pos hm, if_neg hd0]
        have := ih (hi - (lo + hi + 1) / 2) (by omega) _ hi rfl
        have := key (hi - (lo + hi + 1) / 2) (by omega)
        dsimp only
        omega
      · rw [if_neg hm, if_neg hd0]
        have := ih ((lo + hi + 1) / 2 - 1 - lo) (by omega) lo _ rfl
        have := key ((lo + hi + 1) / 2 - 1 - lo) (by omega)
        dsimp only
        omega
    · rw [if_neg h]
      simp

open Classical in
/-- **The node selection**: one comparison `L < H`; for `L < H` the binary search over the cell
boundaries `L + gΔ ≤ s`, `Δ = (H − L)/J`; for `H ≤ L` the node `0`. -/
noncomputable def selectNode (J : ℕ) (L H s : ℝ) : ℕ × ℕ :=
  if L < H then
    ((bsearch (fun g => L + g * ((H - L) / J) ≤ s) 0 (J - 1)).1,
      (bsearch (fun g => L + g * ((H - L) / J) ≤ s) 0 (J - 1)).2 + 1)
  else (0, 1)

/-- **The node selection returns `nodeIdx`.** -/
theorem selectNode_eq {J : ℕ} (hJ : 1 ≤ J) (L H s : ℝ) :
    (selectNode J L H s).1 = nodeIdx J L H s := by
  unfold selectNode nodeIdx
  by_cases hLH : L < H
  · rw [if_pos hLH]
    have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
    set Δ := (H - L) / (J : ℝ) with hΔ
    have hΔp : 0 < Δ := div_pos (by linarith) hJr
    have hH : H = L + J * Δ := by rw [hΔ]; field_simp; ring
    have hmono : ∀ a b : ℕ, a ≤ b → L + b * Δ ≤ s → L + a * Δ ≤ s := by
      intro a b hab hb
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      nlinarith
    obtain ⟨-, h2, h3, h4⟩ := bsearch_spec (fun g => L + g * Δ ≤ s) hmono (J - 1) 0 (J - 1)
      (by omega) (by omega)
    set r := (bsearch (fun g => L + g * Δ ≤ s) 0 (J - 1)).1 with hr
    set x := (max L (min H s) - L) / Δ with hx
    have hx0 : 0 ≤ x := div_nonneg (by have := le_max_left L (min H s); linarith) hΔp.le
    -- `r ≤ ⌊x⌋₊`
    have hrx : r ≤ ⌊x⌋₊ := by
      rcases h3 with h3 | h3
      · rw [h3]; exact Nat.zero_le _
      · apply Nat.le_floor
        rw [hx, le_div_iff₀ hΔp]
        have hrJ : (r : ℝ) ≤ J := by exact_mod_cast (show r ≤ J by omega)
        have h5 : L + r * Δ ≤ H := by rw [hH]; nlinarith
        have h6 : L + r * Δ ≤ min H s := le_min h5 h3
        have h7 := le_trans h6 (le_max_right L (min H s))
        linarith
    apply le_antisymm
    · exact le_min (by omega) hrx
    · by_cases hrJ : r < J - 1
      · have hn := h4 (r + 1) (by omega) (by omega)
        simp only [not_le] at hn
        have hlt : x < (r + 1 : ℕ) := by
          rw [hx, div_lt_iff₀ hΔp]
          have h8 : min H s < L + ((r + 1 : ℕ) : ℝ) * Δ := lt_of_le_of_lt (min_le_right _ _) hn
          have h9 : L < L + ((r + 1 : ℕ) : ℝ) * Δ := by
            have : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
            nlinarith
          linarith [max_lt_iff.mpr ⟨h9, h8⟩]
        have := (Nat.floor_lt hx0).mpr hlt
        omega
      · omega
  · rw [if_neg hLH]
    have hden : (H - L) / (J : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.mp hLH]) (Nat.cast_nonneg _)
    have hnum : 0 ≤ max L (min H s) - L := by have := le_max_left L (min H s); linarith
    have hq : (max L (min H s) - L) / ((H - L) / (J : ℝ)) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hnum hden
    have : ⌊(max L (min H s) - L) / ((H - L) / (J : ℝ))⌋₊ = 0 :=
      Nat.floor_eq_zero.mpr (by linarith)
    rw [this]
    simp

/-- **The number of comparisons of the node selection.** -/
theorem selectNode_count (J : ℕ) (L H s : ℝ) :
    (selectNode J L H s).2 ≤ Nat.log 2 J + 2 := by
  unfold selectNode
  by_cases hLH : L < H
  · rw [if_pos hLH]
    have h := bsearch_count (fun g => L + g * ((H - L) / J) ≤ s) (J - 1 - 0) 0 (J - 1) rfl
    have hm : Nat.log 2 (J - 1 - 0) ≤ Nat.log 2 J := Nat.log_mono_right (by omega)
    simp only
    split_ifs at h <;> omega
  · rw [if_neg hLH]; omega

/-! ## The hit -/

/-- The inputs of the hit program: `![f̃, ω̃, √e_b, t]`, `c_A`, `η`, the weights of `F`. -/
abbrev HitIn (n m : ℕ) : Type := Fin 4 ⊕ (Fin n ⊕ (Fin n ⊕ MlpW n m 1))

def hitVal {n m : ℕ} (f ω rb t : ℝ) (cA η : Fin n → ℝ) (F : MlpParam n m 1) : HitIn n m → ℝ :=
  Sum.elim ![f, ω, rb, t] (Sum.elim cA (Sum.elim η (mlpW F)))

/-- `λ̃ = f̃/√e_b`. -/
def lamE (n m : ℕ) : RExpr (HitIn n m) := RExpr.div (.inp (Sum.inl 0)) (.inp (Sum.inl 2))

/-- `√S̃`, `S̃ = (2/n)(1/5 + relu(ω̃ − f̃·f̃ − 1/5))`. -/
def rsE (n m : ℕ) : RExpr (HitIn n m) :=
  RExpr.sqrt (RExpr.mul (.cst (2 / n)) (RExpr.add (.cst (1 / 5)) (RExpr.relu
    (RExpr.sub (RExpr.sub (.inp (Sum.inl 1)) (RExpr.mul (.inp (Sum.inl 0)) (.inp (Sum.inl 0))))
      (.cst (1 / 5))))))

/-- `y_i = λ̃ c_{A,i} + √S̃ η_i`. -/
def yE (n m : ℕ) (i : Fin n) : RExpr (HitIn n m ⊕ (Unit ⊕ Unit)) :=
  RExpr.add (RExpr.mul (.inp (Sum.inr (Sum.inl ()))) (.inp (Sum.inl (Sum.inr (Sum.inl i)))))
    (RExpr.mul (.inp (Sum.inr (Sum.inr ()))) (.inp (Sum.inl (Sum.inr (Sum.inr (Sum.inl i))))))

def yProg (n m : ℕ) : RProg (HitIn n m) (Fin n) :=
  (RProg.ext (lamE n m).prog ((rsE n m).prog.mapIn Sum.inl)).bind
    (RProg.parF fun i => (yE n m i).prog)

/-- `F(y)`. -/
def fyProg (n m : ℕ) : RProg (HitIn n m) (Fin 1) :=
  (yProg n m).mlpStep (fun e => Sum.inr (Sum.inr (Sum.inr e)))

/-- `relu(F(y) − t)`. -/
def rE (n m : ℕ) : RExpr (HitIn n m ⊕ Fin 1) :=
  RExpr.relu (RExpr.sub (.inp (Sum.inr 0)) (.inp (Sum.inl (Sum.inl 3))))

/-- **The hit program**: `relu(F(y) − t)/relu(F(y) − t)`. -/
def hitProg (n m : ℕ) : RProg (HitIn n m) Unit :=
  ((fyProg n m).bind (rE n m).prog).bind
    (RExpr.div (.inp (Sum.inr ())) (.inp (Sum.inr ()))).prog

theorem yProg_eval {n m : ℕ} (f ω rb t : ℝ) (cA η : Fin n → ℝ) (F : MlpParam n m 1) :
    (yProg n m).eval (hitVal f ω rb t cA η F) =
      (f / rb) • cA + √(2 / (n : ℝ) * max (1 / 5) (ω - f ^ 2)) • η := by
  funext i
  rw [yProg, RProg.eval_bind, RProg.eval_parF, RExpr.eval_prog]
  simp only [yE, RExpr.eval_add, RExpr.eval_mul, RExpr.eval_inp, Sum.elim_inr, Sum.elim_inl,
    RProg.eval_ext_inl, RProg.eval_ext_inr, RProg.eval_mapIn, RExpr.eval_prog]
  have hc : (Sum.elim (hitVal f ω rb t cA η F) ((lamE n m).prog.eval (hitVal f ω rb t cA η F)) ∘
      Sum.inl) = hitVal f ω rb t cA η F := rfl
  try rw [hc]
  simp only [lamE, rsE, RExpr.eval_div, RExpr.eval_sqrt, RExpr.eval_mul, RExpr.eval_add,
    RExpr.eval_relu, RExpr.eval_sub, RExpr.eval_inp, RExpr.eval_cst, hitVal, Sum.elim_inl,
    Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hmax : ((1 / 5 : ℚ) : ℝ) + relu (ω - f * f - ((1 / 5 : ℚ) : ℝ)) = max (1 / 5) (ω - f ^ 2) := by
    unfold relu
    push_cast
    rw [pow_two]
    rcases le_total (ω - f * f) (1 / 5) with h | h
    · rw [max_eq_left (by linarith), max_eq_left h]; ring
    · rw [max_eq_right (by linarith), max_eq_right h]; ring
  rw [hmax]
  have h2 : Matrix.vecHead (Matrix.vecTail ![ω, rb, t]) = rb := rfl
  try simp only [h2]
  push_cast
  ring

theorem hitProg_eval {n m : ℕ} (f ω rb t : ℝ) (cA η : Fin n → ℝ) (F : MlpParam n m 1) :
    (hitProg n m).eval (hitVal f ω rb t cA η F) () =
      if t < mlpEval F ((f / rb) • cA + √(2 / (n : ℝ) * max (1 / 5) (ω - f ^ 2)) • η) 0
      then 1 else 0 := by
  rw [hitProg, RProg.eval_bind, RExpr.eval_prog]
  simp only [RExpr.eval_div, RExpr.eval_inp, Sum.elim_inr]
  rw [RProg.eval_bind, RExpr.eval_prog]
  simp only [rE, RExpr.eval_relu, RExpr.eval_sub, RExpr.eval_inp, Sum.elim_inr, Sum.elim_inl]
  rw [ind_pos, fyProg, RProg.eval_mlpStep (yProg n m) (fun e => Sum.inr (Sum.inr (Sum.inr e)))
    (hitVal f ω rb t cA η F) F (fun _ => rfl), yProg_eval]
  simp only [hitVal, Sum.elim_inl, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    sub_pos]

theorem hitProg_cost (n m : ℕ) : (hitProg n m).cost = 3 * n + 11 + mlpCost n m 1 := by
  simp only [hitProg, fyProg, yProg, RProg.cost_bind, RProg.cost_mlpStep, RProg.cost_ext,
    RProg.cost_mapIn, RExpr.cost_prog]
  rw [RProg.cost_parF_eq _ 3 (fun i => by simp [yE])]
  simp [lamE, rsE, rE]
  ring

/-! ## The link with one draw of the program -/

/-- `ρ = √(|ĉ|² + nτ₀²)` of the retained data (Part 150 `rhoC`). -/
abbrev rhoC' {n : ℕ} (c : Ret n) : ℝ := BstLean.Part150.rhoC c.1.2 (tau0p c.1.1)

/-- **One draw of the program is the hit program at the selected node.** For the design
`paperDesign n fT wT` (`statedDesign n` is one), the value `hitFn` of a draw `d` is `hitProg` with
the table values at the node `nodeIdx (Js n) L H s` of the latitude `s`. -/
theorem hitFn_eq_hitProg {n : ℕ} (fT wT : Ret n → ℕ → ℝ) (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) (c : Ret n) (d : DrawSp n) :
    hitFn (paperDesign n fT wT hf hw) t (c, d) =
      (hitProg n (mF n)).eval
        (hitVal
          (fT c (nodeIdx (Js n)
            (√(normSq c.1.2) / rhoC' c - 6 * tau0p c.1.1 / rhoC' c)
            (√(normSq c.1.2) / rhoC' c + 6 * tau0p c.1.1 / rhoC' c)
            (latitude (√(normSq c.1.2)) (tau0p c.1.1) d.1)))
          (wT c (nodeIdx (Js n)
            (√(normSq c.1.2) / rhoC' c - 6 * tau0p c.1.1 / rhoC' c)
            (√(normSq c.1.2) / rhoC' c + 6 * tau0p c.1.1 / rhoC' c)
            (latitude (√(normSq c.1.2)) (tau0p c.1.1) d.1)))
          (√(normSq (bAp c.1 c.2.1.1) / (n : ℝ))) t c.2.1.2 d.2 c.2.2) () := by
  rw [hitProg_eval]
  unfold hitFn hitEv
  simp only [Set.indicator, Set.mem_setOf_eq, classifier, drawY, Pi.one_apply]
  rfl

end

end BstLean.Part282

/-- info: 'BstLean.Part282.hitFn_eq_hitProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.hitFn_eq_hitProg
/-- info: 'BstLean.Part282.selectNode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.selectNode_eq
/-- info: 'BstLean.Part282.latProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.latProg_eval
