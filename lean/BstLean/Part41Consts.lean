import BstLean.Part41Defs

/-!
# Part 41, wave 1: the moment constants are computed by the program (replaces Lemma `MC`)

Paper: Lemma `MC` and Definition `cost`; rule A3 of `solution-plans/option-m.md` (the moments are
computed by `g`, charged). Specification: `delegations/answers/p41-spec-opus.md`, flag 2.
Do not use `native_decide`.

Routes.
* `inline_consts`: build every heavy constant `a/b` from `1` before the program (binary
  double-and-add: an integer `< 2^β` takes `≤ 2(β − 1)` operations; then `0 − a` and `a / b`), then run the
  program with each heavy constant replaced by the input of its register (`Prog.bind`, `eval_bind`).
* `gProgL_heights`: every heavy constant is a weight `wKey K key`. Its denominator divides
  `ρ_{kd}(n) ∏ (D + …)` (each `sphMomQ e` has denominator dividing `ρ_{|e|/2}(n) | ρ_{kd}(n)`; `c_{j,l}` is an
  integer; the factors of `κ` and `μ` are integers in `[D, D + 2k]`), and `|wKey| ≤ (k!)³ N^k`
  (`HQ_bounds`; `orbSize q ≤ (card q)!`).
-/

namespace BstLean.Part41

open BstLean.Cost
open BstLean.Part36 (CoefIdxD)

variable {n d : ℕ}

private def Light {ι : Type} (a : Arg ι) : Prop :=
  ∀ q, a = .cst q → q = 0 ∨ q = 1

private def LightProg {ι κ : Type} (p : Prog ι κ) : Prop :=
  (∀ I ∈ p.body, Light I.a ∧ Light I.b) ∧ ∀ o, Light (p.out o)

private lemma light_inp {ι : Type} (i : ι) : Light (.inp i) := by
  intro q h; cases h

private lemma light_reg {ι : Type} (r : ℕ) : Light (Arg.reg (ι := ι) r) := by
  intro q h; cases h

private lemma light_zero {ι : Type} : Light (Arg.cst (ι := ι) 0) := by
  intro q h; cases h; exact Or.inl rfl

private lemma light_one {ι : Type} : Light (Arg.cst (ι := ι) 1) := by
  intro q h; cases h; exact Or.inr rfl

private lemma light_rename {ι ι' : Type} (a : Arg ι) (h : Light a) (σ : ι → ι') :
    Light (a.rename σ) := by
  cases a with
  | inp i => exact light_inp _
  | reg r => exact light_reg _
  | cst q => intro r hr; cases hr; exact h q rfl

private lemma light_clamp {ι : Type} (a : Arg ι) (h : Light a) (s : ℕ) :
    Light (a.clamp s) := by
  cases a with
  | inp i => exact light_inp _
  | reg r => simp only [Arg.clamp]; split <;> first | exact light_reg _ | exact light_zero
  | cst q => exact h

private lemma light_subst {ι ι' : Type} (a : Arg ι) (h : Light a)
    (σ : ι → Arg ι') (hσ : ∀ i, Light (σ i)) (s len : ℕ) :
    Light (a.subst σ s len) := by
  cases a with
  | inp i => exact hσ i
  | reg r => simp only [Arg.subst]; split <;> first | exact light_reg _ | exact light_zero
  | cst q =>
    intro r hr
    have he : q = r := Arg.cst.inj hr
    subst r
    exact h q rfl

private lemma light_bind {ι κ ν : Type} (p : Prog ι κ) (q : Prog (ι ⊕ κ) ν)
    (hp : LightProg p) (hq : LightProg q) : LightProg (p.bind q) := by
  let σ : ι ⊕ κ → Arg ι := Sum.elim Arg.inp (fun o => (p.out o).clamp p.body.length)
  have hs : ∀ i, Light (σ i) := by
    intro i; cases i with
    | inl i => exact light_inp _
    | inr o => exact light_clamp _ (hp.2 o) _
  constructor
  · intro I hI
    simp only [Prog.bind, List.mem_append, List.mem_map] at hI
    rcases hI with hI | ⟨J, hJ, rfl⟩
    · exact hp.1 I hI
    · exact ⟨light_subst _ (hq.1 J hJ).1 σ hs _ _,
        light_subst _ (hq.1 J hJ).2 σ hs _ _⟩
  · intro o
    exact light_subst _ (hq.2 o) σ hs _ _

private lemma light_op {ι : Type} (op : Op) (a b : Arg ι) (ha : Light a) (hb : Light b) :
    LightProg (Prog.op1 op a b) := by
  constructor
  · intro I hI; simp only [Prog.op1, List.mem_singleton] at hI; subst I; exact ⟨ha, hb⟩
  · intro o; exact light_reg _

private lemma light_ofArgs {ι κ : Type} (a : κ → Arg ι) (h : ∀ o, Light (a o)) :
    LightProg (Prog.ofArgs a) := ⟨by simp [Prog.ofArgs], h⟩

private lemma light_heavy_zero {ι κ : Type} [Fintype κ] (p : Prog ι κ)
    (hp : LightProg p) : heavyCount p = 0 := by
  have ha : ∀ a : Arg ι, Light a → argHeavy a = 0 := by
    intro a h; cases a with
    | inp i => rfl
    | reg r => rfl
    | cst q => simp [argHeavy, h q rfl]
  unfold heavyCount
  have hb : (p.body.map fun I => argHeavy I.a + argHeavy I.b).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hx
    simp [ha _ (hp.1 I hI).1, ha _ (hp.1 I hI).2]
  rw [hb]
  simp [ha _ (hp.2 _)]

/-- Binary synthesis, retaining a two-operation margin for the sign and division. -/
private lemma nat_program {ι : Type} (β a : ℕ) (ha : a < 2 ^ β) :
    ∃ p : Prog ι Unit, LightProg p ∧ (∀ v, p.eval v () = (a : ℝ)) ∧
      p.cost ≤ 2 * (β - 1) := by
  induction β generalizing a with
  | zero =>
    have : a = 0 := by simpa using ha
    subst a
    exact ⟨Prog.ofArgs (fun _ => .cst 0), light_ofArgs _ (fun _ => light_zero),
      by simp [Arg.eval], by simp⟩
  | succ β ih =>
    by_cases hb : β = 0
    · subst β
      have : a = 0 ∨ a = 1 := by norm_num at ha; omega
      rcases this with rfl | rfl
      · exact ⟨Prog.ofArgs (fun _ => .cst 0), light_ofArgs _ (fun _ => light_zero),
          by simp [Arg.eval], by simp⟩
      · exact ⟨Prog.ofArgs (fun _ => .cst 1), light_ofArgs _ (fun _ => light_one),
          by simp [Arg.eval], by simp⟩
    have hhalf : a / 2 < 2 ^ β := by
      rw [Nat.pow_succ] at ha
      omega
    obtain ⟨p, hp, he, hc⟩ := ih (a / 2) hhalf
    let q : Prog (ι ⊕ Unit) Unit := Prog.op1 .add (.inp (.inr ())) (.inp (.inr ()))
    have hq : LightProg q := light_op _ _ _ (light_inp _) (light_inp _)
    by_cases hr : a % 2 = 0
    · refine ⟨p.bind q, light_bind _ _ hp hq, ?_, ?_⟩
      · intro v
        simp [q, eval_bind, Arg.eval, Op.eval, he]
        have hh : a = a / 2 + a / 2 := by omega
        exact_mod_cast hh.symm
      · simp only [cost_bind, q, cost_op1]
        omega
    · let r : Prog (ι ⊕ Unit) Unit := Prog.op1 .add (.inp (.inr ())) (.cst 1)
      refine ⟨(p.bind q).bind r, light_bind _ _ (light_bind _ _ hp hq)
        (light_op _ _ _ (light_inp _) light_one), ?_, ?_⟩
      · intro v
        simp [r, q, eval_bind, Arg.eval, Op.eval, he]
        have hh : a = a / 2 + a / 2 + 1 := by omega
        exact_mod_cast hh.symm
      · simp only [cost_bind, q, r, cost_op1]
        omega

private lemma light_par {ι κ : Type} [DecidableEq κ] (p : κ → Prog ι Unit)
    (l : List κ) (hp : ∀ o ∈ l, LightProg (p o)) : LightProg (Prog.par p l) := by
  induction l with
  | nil => exact light_ofArgs _ (fun _ => light_zero)
  | cons o l ih =>
    apply light_bind _ _ (hp o (by simp))
    have ht := ih (fun a ha => hp a (by simp [ha]))
    constructor
    · intro I hI
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
      have hr : ∀ a : Arg ι, Light a → Light (a.rename (Sum.inl : ι → ι ⊕ Unit)) := by
        intro a ha; cases a with
        | inp i => exact light_inp _
        | reg r => exact light_reg _
        | cst q => intro r hr; cases hr; exact ha q rfl
      exact ⟨hr _ (ht.1 J hJ).1, hr _ (ht.1 J hJ).2⟩
    · intro j
      simp only
      split
      · exact light_inp _
      · exact light_rename _ (ht.2 j) _

private lemma rat_program {ι : Type} (β : ℕ) (q : ℚ)
    (ha : q.num.natAbs < 2 ^ β) (hd : q.den < 2 ^ β) :
    ∃ p : Prog ι Unit, LightProg p ∧ (∀ v, p.eval v () = (q : ℝ)) ∧ p.cost ≤ 4 * β := by
  have hb : 1 ≤ β := by
    by_contra h
    have hβ : β = 0 := by omega
    have hpos := q.den_pos
    simp [hβ] at hd
  obtain ⟨a, hla, hea, hca⟩ := nat_program (ι := ι) β q.num.natAbs ha
  obtain ⟨b, hlb, heb, hcb⟩ := nat_program (ι := ι) β q.den hd
  have hi : ∃ a' : Prog ι Unit, LightProg a' ∧
      (∀ v, a'.eval v () = (q.num : ℝ)) ∧ a'.cost ≤ 2 * (β - 1) + 1 := by
    by_cases hs : 0 ≤ q.num
    · refine ⟨a, hla, ?_, by omega⟩
      intro v; rw [hea]
      have hh : (q.num.natAbs : ℤ) = q.num := by omega
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hh
    · let neg : Prog (ι ⊕ Unit) Unit := Prog.op1 .sub (.cst 0) (.inp (.inr ()))
      refine ⟨a.bind neg, light_bind _ _ hla (light_op _ _ _ light_zero (light_inp _)), ?_, ?_⟩
      · intro v
        simp only [eval_bind, neg, eval_op1, Op.eval, Arg.eval, Sum.elim_inr, hea]
        have hh : -(q.num.natAbs : ℤ) = q.num := by omega
        have hh' : -(q.num.natAbs : ℝ) = (q.num : ℝ) := by exact_mod_cast hh
        simpa using hh'
      · simp only [cost_bind, neg, cost_op1]; omega
  obtain ⟨a', hla', hea', hca'⟩ := hi
  have hlpair : LightProg (a'.pair b) := by
    apply light_bind _ _ hla'
    constructor
    · intro I hI
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
      constructor <;> intro r hr
      · cases h : J.a <;> simp [Instr.rename, Arg.rename, h] at hr
        subst r; exact (hlb.1 J hJ).1 _ h
      · cases h : J.b <;> simp [Instr.rename, Arg.rename, h] at hr
        subst r; exact (hlb.1 J hJ).2 _ h
    · intro o; cases o with
      | inl o => exact light_inp _
      | inr o =>
        intro r hr
        cases h : b.out o <;> simp [Prog.mapIn, Arg.rename, h] at hr
        subst r; exact hlb.2 o _ h
  let div : Prog (ι ⊕ (Unit ⊕ Unit)) Unit :=
    Prog.op1 .div (.inp (.inr (.inl ()))) (.inp (.inr (.inr ())))
  refine ⟨(a'.pair b).bind div, light_bind _ _ hlpair
    (light_op _ _ _ (light_inp _) (light_inp _)), ?_, ?_⟩
  · intro v
    simp only [eval_bind, div, eval_op1, Op.eval, Arg.eval, Sum.elim_inr,
      eval_pair_inl, eval_pair_inr, hea', heb]
    exact_mod_cast q.num_div_den
  · simp only [cost_bind, cost_pair, div, cost_op1]; omega

private noncomputable def args {ι κ : Type} [Fintype κ] (p : Prog ι κ) : List (Arg ι) :=
  (p.body.flatMap fun I => [I.a, I.b]) ++ (Finset.univ : Finset κ).toList.map p.out

private noncomputable def collect {ι : Type} : Arg ι → Option ℚ
  | .cst q => if q = 0 ∨ q = 1 then none else some q
  | _ => none

private lemma heavy_length {ι κ : Type} [Fintype κ] (p : Prog ι κ) :
    (heavyConsts p).length = heavyCount p := by
  have hl : ∀ l : List (Arg ι), (l.filterMap collect).length = (l.map argHeavy).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      cases a with
      | inp i => simpa [List.filterMap_cons, collect, argHeavy] using ih
      | reg r => simpa [List.filterMap_cons, collect, argHeavy] using ih
      | cst q => by_cases h : q = 0 ∨ q = 1 <;> simp [collect, argHeavy, h, ih, Nat.add_comm]
  change ((args p).filterMap collect).length = _
  rw [hl]
  have hb : ((p.body.flatMap fun I => [I.a, I.b]).map argHeavy).sum =
      (p.body.map fun I => argHeavy I.a + argHeavy I.b).sum := by
    induction p.body with
    | nil => rfl
    | cons I l ih => simp [ih, Nat.add_assoc]
  simp only [args, List.map_append, List.sum_append, List.map_map]
  rw [hb]
  congr 1
  simp

private lemma arg_mem_body {ι κ : Type} [Fintype κ] (p : Prog ι κ) (I : Instr ι)
    (hI : I ∈ p.body) : I.a ∈ args p ∧ I.b ∈ args p := by
  constructor <;> apply List.mem_append_left <;> apply List.mem_flatMap.mpr
  · exact ⟨I, hI, by simp⟩
  · exact ⟨I, hI, by simp⟩

private lemma arg_mem_out {ι κ : Type} [Fintype κ] (p : Prog ι κ) (o : κ) :
    p.out o ∈ args p := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨o, by simp, rfl⟩

private noncomputable def replace {ι : Type} (l : List ℚ) : Arg ι → Arg (ι ⊕ Fin l.length)
  | .inp i => .inp (.inl i)
  | .reg r => .reg r
  | .cst q => if q = 0 ∨ q = 1 then .cst q else
      if h : q ∈ l then .inp (.inr ⟨l.idxOf q, List.idxOf_lt_length_of_mem h⟩) else .cst 0

private lemma replace_light {ι : Type} (l : List ℚ) (a : Arg ι) : Light (replace l a) := by
  cases a with
  | inp i => exact light_inp _
  | reg r => exact light_reg _
  | cst q =>
    simp only [replace]
    split_ifs with h hm
    · intro r hr; cases hr; exact h
    · exact light_inp _
    · exact light_zero

private noncomputable def replaceProg {ι κ : Type} (l : List ℚ) (p : Prog ι κ) :
    Prog (ι ⊕ Fin l.length) κ :=
  ⟨p.body.map (fun I => ⟨I.op, replace l I.a, replace l I.b⟩), fun o => replace l (p.out o)⟩

private lemma replaceProg_light {ι κ : Type} (l : List ℚ) (p : Prog ι κ) :
    LightProg (replaceProg l p) := by
  constructor
  · intro I hI
    obtain ⟨J, _, rfl⟩ := List.mem_map.mp hI
    exact ⟨replace_light _ _, replace_light _ _⟩
  · intro o; exact replace_light _ _

private lemma replace_eval {ι κ : Type} [Fintype κ] (p : Prog ι κ) (v : ι → ℝ)
    (u : Fin (heavyConsts p).length → ℝ) (hu : ∀ i, u i = ((heavyConsts p).get i : ℝ))
    (a : Arg ι) (ha : a ∈ args p) (R : List ℝ) :
    (replace (heavyConsts p) a).eval (Sum.elim v u) R = a.eval v R := by
  cases a with
  | inp i => rfl
  | reg r => rfl
  | cst q =>
    simp only [replace]
    split_ifs with h hm
    · rfl
    · simp only [Arg.eval, Sum.elim_inr, hu, List.get_eq_getElem, List.getElem_idxOf]
    · have hq : q ∈ heavyConsts p := by
        change q ∈ (args p).filterMap collect
        exact List.mem_filterMap.mpr ⟨.cst q, ha, by simp [collect, h]⟩
      exact (hm hq).elim

private lemma replaceProg_eval {ι κ : Type} [Fintype κ] (p : Prog ι κ) (v : ι → ℝ)
    (u : Fin (heavyConsts p).length → ℝ) (hu : ∀ i, u i = ((heavyConsts p).get i : ℝ)) :
    ∀ o, (replaceProg (heavyConsts p) p).eval (Sum.elim v u) o = p.eval v o := by
  have hr : ∀ (l : List (Instr ι)), (∀ I ∈ l, I ∈ p.body) → ∀ R,
      run (Sum.elim v u) (l.map fun I => ⟨I.op, replace (heavyConsts p) I.a,
        replace (heavyConsts p) I.b⟩) R = run v l R := by
    intro l
    induction l with
    | nil => simp [run]
    | cons I l ih =>
      intro hl R
      have hI := arg_mem_body p I (hl I (by simp))
      simp only [List.map_cons, run, Instr.eval]
      rw [replace_eval p v u hu I.a hI.1, replace_eval p v u hu I.b hI.2]
      exact ih (fun J hJ => hl J (by simp [hJ])) _
  intro o
  simp only [replaceProg, Prog.eval]
  rw [hr p.body (fun _ h => h)]
  exact replace_eval p v u hu _ (arg_mem_out p o) _

/-- **Inline the heavy constants**: if every heavy constant has `|num|, den < 2^β`, an equivalent program
uses only the constants `0` and `1`, with at most `4β` more operations per heavy constant. -/
theorem inline_consts {ι κ : Type} [Fintype κ] (p : Prog ι κ) (β : ℕ)
    (hb : ∀ q ∈ heavyConsts p, q.num.natAbs < 2 ^ β ∧ q.den < 2 ^ β) :
    ∃ p' : Prog ι κ, heavyCount p' = 0 ∧ (∀ v o, p'.eval v o = p.eval v o) ∧
      p'.cost ≤ p.cost + 4 * β * heavyCount p := by
  classical
  let l := heavyConsts p
  have hs : ∀ i : Fin l.length, ∃ a : Prog ι Unit, LightProg a ∧
      (∀ v, a.eval v () = (l.get i : ℝ)) ∧ a.cost ≤ 4 * β := by
    intro i
    have hi : l.get i ∈ heavyConsts p := List.get_mem _ _
    exact rat_program β _ (hb _ hi).1 (hb _ hi).2
  choose a hla hea hca using hs
  let pre := Prog.par a (List.finRange l.length)
  refine ⟨pre.bind (replaceProg l p), ?_, ?_, ?_⟩
  · apply light_heavy_zero
    exact light_bind _ _ (light_par _ _ (fun i _ => hla i)) (replaceProg_light _ _)
  · intro v o
    rw [eval_bind]
    apply replaceProg_eval p v (pre.eval v) _ o
    intro i
    rw [eval_par_mem a _ v i (List.mem_finRange i)]
    exact hea i v
  · have hp : pre.cost ≤ 4 * β * l.length := by
      rw [cost_par]
      calc
        ((List.finRange l.length).map fun i => (a i).cost).sum ≤
            ((List.finRange l.length).map fun _ => 4 * β).sum := by
          apply List.sum_le_sum
          intro i hi
          exact hca i
        _ = 4 * β * l.length := by simp [Nat.mul_comm]
    have hcost : (replaceProg l p).cost = p.cost := by simp [replaceProg, Prog.cost]
    rw [cost_bind, hcost]
    have hlen : l.length = heavyCount p := heavy_length p
    conv at hp => rhs; rw [hlen]
    omega


private lemma cQ_nat (j l : ℕ) (hl : 2 * l ≤ j) :
    cQ j l = ((j.choose (2 * l) * (2 * l - 1).doubleFactorial : ℕ) : ℚ) := by
  have hf : (2 * l).factorial = 2 ^ l * l.factorial * (2 * l - 1).doubleFactorial := by
    by_cases hz : l = 0
    · subst l; simp
    · have he : 2 * l - 1 + 1 = 2 * l := by omega
      have h := Nat.factorial_eq_mul_doubleFactorial (2 * l - 1)
      rw [he, Nat.doubleFactorial_two_mul] at h
      exact h
  have hc := Nat.choose_mul_factorial_mul_factorial hl
  rw [hf] at hc
  unfold cQ
  apply (div_eq_iff (by positivity :
    (l.factorial : ℚ) * 2 ^ l * ((j - 2 * l).factorial : ℚ) ≠ 0)).mpr
  have hq : (j.choose (2 * l) : ℚ) * (2 ^ l * (l.factorial : ℚ) *
      ((2 * l - 1).doubleFactorial : ℚ)) * ((j - 2 * l).factorial : ℚ) = (j.factorial : ℚ) := by
    exact_mod_cast hc
  push_cast
  linear_combination -hq

private lemma cQ_bounds (j l : ℕ) :
    0 ≤ cQ j l ∧ cQ j l ≤ (j.factorial : ℚ) := by
  constructor
  · unfold cQ; positivity
  · unfold cQ
    have hden : (1 : ℚ) ≤ (l.factorial : ℚ) * 2 ^ l * ((j - 2 * l).factorial : ℚ) := by
      have h1 : (1 : ℚ) ≤ (l.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos l
      have h2 : (1 : ℚ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
      have h3 : (1 : ℚ) ≤ ((j - 2 * l).factorial : ℚ) := by
        exact_mod_cast Nat.factorial_pos (j - 2 * l)
      nlinarith [mul_le_mul h1 h2 (by positivity) (by positivity),
        mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)]
    exact div_le_self (by positivity) hden

private def rhoNat (n m : ℕ) : ℕ := ∏ t ∈ Finset.range m, (n + 2 * t)

private lemma rhoQ_cast (n m : ℕ) : rhoQ n m = (rhoNat n m : ℚ) := by
  simp [rhoQ, rhoNat, Nat.cast_prod, Nat.cast_add, Nat.cast_mul]

private lemma rhoNat_pos (hn : 1 ≤ n) (m : ℕ) : 0 < rhoNat n m := by
  unfold rhoNat
  exact Finset.prod_pos (fun t _ => by omega)

private lemma rhoNat_dvd (n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    rhoNat n a ∣ rhoNat n b := by
  unfold rhoNat
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hab)

private lemma rat_nat_div_den_dvd (a b : ℕ) : ((a : ℚ) / (b : ℚ)).den ∣ b := by
  have h : (a : ℚ) / (b : ℚ) = Rat.divInt (a : ℤ) (b : ℤ) := by
    simp [Rat.divInt_eq_div]
  rw [h]
  exact_mod_cast Rat.den_dvd (a : ℤ) (b : ℤ)

private lemma sphMom_den_dvd (e : Fin n → ℕ) :
    (sphMomQ e).den ∣ rhoNat n ((∑ a, e a) / 2) := by
  classical
  unfold sphMomQ
  split_ifs with he
  · rw [rhoQ_cast]
    have hprod : (∏ a, ((e a - 1).doubleFactorial : ℚ)) =
        ((∏ a, (e a - 1).doubleFactorial : ℕ) : ℚ) := by simp
    rw [hprod]
    exact rat_nat_div_den_dvd _ _
  · simp

private lemma sum_den_dvd {α : Type} (s : Finset α) (f : α → ℚ) (R : ℕ)
    (hf : ∀ a ∈ s, (f a).den ∣ R) : (∑ a ∈ s, f a).den ∣ R := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (Rat.add_den_dvd_lcm _ _).trans
      (Nat.lcm_dvd (hf a (by simp)) (ih (fun b hb => hf b (by simp [hb]))))

private lemma sum_expo (p : Mono n d) : ∑ a, expo p a = p.1.val := by
  classical
  unfold expo
  have h : ∑ a : Fin n, p.2.1.count a = p.2.1.card :=
    Multiset.sum_count_eq_card (by simp)
  rw [h]
  exact p.2.2

private lemma HQ_den_dvd {s : ℕ} (l k : ℕ) (hsk : s + 2 * l ≤ k)
    (w : Fin s → Mono n d) : (HQ l w).den ∣ rhoNat n (k * d) := by
  classical
  unfold HQ
  apply sum_den_dvd
  intro c _
  apply (sphMom_den_dvd _).trans
  apply rhoNat_dvd
  have he : (∑ a : Fin n, ((∑ t : Fin l, 2 * expo (c t) a) +
      ∑ t : Fin s, expo (w t) a)) ≤ k * d := by
    rw [Finset.sum_add_distrib]
    have hc : (∑ a : Fin n, ∑ t : Fin l, 2 * expo (c t) a) ≤ 2 * l * d := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ t : Fin l, 2 * (c t).1.val := by
          congr 1; ext t; rw [← Finset.mul_sum, sum_expo]
        _ ≤ ∑ _t : Fin l, 2 * d := by
          apply Finset.sum_le_sum; intro t _
          have := (c t).1.isLt; omega
        _ = 2 * l * d := by simp; ring
    have hw : (∑ a : Fin n, ∑ t : Fin s, expo (w t) a) ≤ s * d := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ t : Fin s, (w t).1.val := by simp_rw [sum_expo]
        _ ≤ ∑ _t : Fin s, d := by
          apply Finset.sum_le_sum; intro t _
          have := (w t).1.isLt; omega
        _ = s * d := by simp
    calc
      _ ≤ 2 * l * d + s * d := Nat.add_le_add hc hw
      _ = (s + 2 * l) * d := by ring
      _ ≤ k * d := Nat.mul_le_mul_right d hsk
  exact (Nat.div_le_self _ 2).trans he

private lemma HKQ_den_dvd {s : ℕ} (K : Finset (Multiset (Mono n d))) (l k : ℕ)
    (hsk : s + 2 * l ≤ k) (w : Fin s → Mono n d) :
    (HKQ K l w).den ∣ rhoNat n (k * d) := by
  classical
  unfold HKQ
  split_ifs
  · exact HQ_den_dvd l k hsk w
  · simp

private lemma trHKQ_den_dvd {s : ℕ} (K : Finset (Multiset (Mono n d))) (l i k : ℕ)
    (hsk : s + 2 * l ≤ k) (w : Fin (s - 2 * i) → Mono n d) :
    (trL i (HKQ K l) w).den ∣ rhoNat n (k * d) := by
  classical
  unfold trL
  apply sum_den_dvd
  intro c _
  exact HKQ_den_dvd K l k hsk _

private lemma rhoQ_pos (hn : 1 ≤ n) (m : ℕ) : 0 < rhoQ n m := by
  unfold rhoQ
  apply Finset.prod_pos
  intro t ht
  have : (0 : ℚ) < n := by exact_mod_cast hn
  positivity

private lemma num_le_rho (hn : 1 ≤ n) (a : Fin n → ℕ) :
    (∏ i, ((2 * a i - 1).doubleFactorial : ℚ)) ≤ rhoQ n (∑ i, a i) := by
  classical
  generalize hm : (∑ i, a i) = m
  induction m using Nat.strong_induction_on generalizing a with
  | h m ih =>
    by_cases hz : m = 0
    · have ha : ∀ i, a i = 0 := by
        intro i
        have := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
        omega
      simp [ha, hz, rhoQ, Nat.doubleFactorial]
    · have hex : ∃ i, a i ≠ 0 := by
        by_contra h
        push Not at h
        simp [h] at hm
        omega
      obtain ⟨i, hi⟩ := hex
      let b := Function.update a i (a i - 1)
      have hb : (∑ j, b j) + 1 = m := by
        have h1 := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) a (Finset.mem_univ i)
        have h2 := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) b (Finset.mem_univ i)
        have he : ∑ j ∈ Finset.univ.erase i, b j = ∑ j ∈ Finset.univ.erase i, a j := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [b, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        have hbi : b i = a i - 1 := by simp [b]
        rw [he, hbi] at h2
        omega
      have hind := ih (∑ j, b j) (by omega) b rfl
      have hp : (∏ j, ((2 * a j - 1).doubleFactorial : ℚ)) =
          (2 * (a i : ℚ) - 1) * ∏ j, ((2 * b j - 1).doubleFactorial : ℚ) := by
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
          ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
        have he : (∏ j ∈ Finset.univ.erase i, ((2 * b j - 1).doubleFactorial : ℚ)) =
            ∏ j ∈ Finset.univ.erase i, ((2 * a j - 1).doubleFactorial : ℚ) := by
          apply Finset.prod_congr rfl
          intro j hj
          simp [b, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        rw [he]
        have hd : (2 * a i - 1).doubleFactorial =
            (2 * a i - 1) * (2 * (a i - 1) - 1).doubleFactorial := by
          obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero hi
          rw [hv]
          simpa [Nat.mul_add, Nat.add_sub_assoc] using Nat.doubleFactorial_add_one (2 * v)
        rw [hd]
        simp only [Nat.cast_mul]
        have hc : ((2 * a i - 1 : ℕ) : ℚ) = 2 * (a i : ℚ) - 1 := by
          rw [Nat.cast_sub (by omega)]; norm_num
        rw [hc]
        simp [b]
        ring
      have hr : rhoQ n m = rhoQ n (∑ j, b j) * ((n : ℚ) + 2 * (∑ j, b j : ℕ)) := by
        rw [← hb]
        simp [rhoQ, Finset.prod_range_succ]
      have hfac : 0 ≤ 2 * (a i : ℚ) - 1 := by
        have : (1 : ℚ) ≤ a i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
        linarith
      have hle : 2 * (a i : ℚ) - 1 ≤ (n : ℚ) + 2 * (∑ j, b j : ℕ) := by
        have hs := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
        have hs' : (a i : ℚ) ≤ m := by exact_mod_cast (hm ▸ hs)
        have hb' : ((∑ j, b j : ℕ) : ℚ) + 1 = m := by exact_mod_cast hb
        have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
        linarith
      rw [hp, hr]
      calc
        _ ≤ (2 * (a i : ℚ) - 1) * rhoQ n (∑ j, b j) := mul_le_mul_of_nonneg_left hind hfac
        _ ≤ _ := by
          rw [mul_comm (rhoQ n _)]
          exact mul_le_mul_of_nonneg_right hle (rhoQ_pos hn _).le

/-- Every entry of `H_{j,l}` is `≥ 0` and `≤ N^l` (each sphere moment is in `[0, 1]`). -/
private lemma const_HQ_bounds {s : ℕ} (l : ℕ) (w : Fin s → Mono n d) :
    0 ≤ HQ l w ∧ HQ l w ≤ (Fintype.card (Mono n d) : ℚ) ^ l := by
  classical
  have hmoment (e : Fin n → ℕ) : 0 ≤ sphMomQ e ∧ sphMomQ e ≤ 1 := by
    by_cases hn : n = 0
    · subst n
      simp [sphMomQ, rhoQ]
    have hn' : 1 ≤ n := by omega
    unfold sphMomQ
    split_ifs with he
    · let a : Fin n → ℕ := fun i => e i / 2
      have ha : ∀ i, e i = 2 * a i := by
        intro i
        obtain ⟨v, hv⟩ := he i
        simp [a, hv, ← two_mul]
      have hs : (∑ i, e i) / 2 = ∑ i, a i := by
        simp_rw [ha]
        rw [← Finset.mul_sum]
        omega
      rw [hs]
      constructor
      · exact div_nonneg (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
          (rhoQ_pos hn' _).le
      · apply (div_le_one (rhoQ_pos hn' _)).mpr
        simpa only [ha] using num_le_rho hn' a
    · norm_num
  unfold HQ
  constructor
  · exact Finset.sum_nonneg (fun c _ => (hmoment _).1)
  · calc
      _ ≤ ∑ _c : Fin l → Mono n d, (1 : ℚ) :=
        Finset.sum_le_sum (fun c _ => (hmoment _).2)
      _ = _ := by simp

private lemma kapQ_den_dvd (j l : ℕ) (hl : 2 * l ≤ j) :
    (kapQ n d j l).den ∣
      ∏ i ∈ Finset.range l, (Fintype.card (CoefIdxD n d) + 2 * (j - 2 * l) + 2 * i) := by
  rw [kapQ, cQ_nat j l hl]
  have hp : (∏ i ∈ Finset.range l, (DQ n d + 2 * ((j - 2 * l : ℕ) : ℚ) + 2 * i)) =
      ((∏ i ∈ Finset.range l,
        (Fintype.card (CoefIdxD n d) + 2 * (j - 2 * l) + 2 * i) : ℕ) : ℚ) := by
    simp [DQ]
  rw [hp]
  exact rat_nat_div_den_dvd _ _

private lemma kapQ_den_le (hn : 1 ≤ n) (j l k : ℕ) (hl : 2 * l ≤ j) (hj : j ≤ k) :
    (kapQ n d j l).den ≤ (Fintype.card (CoefIdxD n d) + 2 * k) ^ l := by
  have hd := kapQ_den_dvd (n := n) (d := d) j l hl
  let a : Fin n := ⟨0, by omega⟩
  let : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, a)⟩⟩
  have hc : 0 < Fintype.card (CoefIdxD n d) := Fintype.card_pos
  have hpos : 0 < ∏ i ∈ Finset.range l,
      (Fintype.card (CoefIdxD n d) + 2 * (j - 2 * l) + 2 * i) :=
    Finset.prod_pos (fun _ _ => by omega)
  calc
    _ ≤ _ := Nat.le_of_dvd hpos hd
    _ ≤ ∏ _i ∈ Finset.range l, (Fintype.card (CoefIdxD n d) + 2 * k) := by
      apply Finset.prod_le_prod
      intro i hi
      have := Finset.mem_range.mp hi
      omega
    _ = _ := by simp

private lemma rat_int_div_den_dvd (a : ℤ) (b : ℕ) : ((a : ℚ) / (b : ℚ)).den ∣ b := by
  have h : (a : ℚ) / (b : ℚ) = Rat.divInt a (b : ℤ) := by
    simp [Rat.divInt_eq_div]
  rw [h]
  exact_mod_cast Rat.den_dvd a (b : ℤ)

private lemma muQ_den_dvd (s i : ℕ) (hi : 2 * i ≤ s) :
    (muQ n d s i).den ∣
      ∏ m ∈ Finset.Icc 1 i, (Fintype.card (CoefIdxD n d) + 2 * s - 2 - 2 * m) := by
  rw [muQ, cQ_nat s i hi]
  have hp : (∏ m ∈ Finset.Icc 1 i, (DQ n d + 2 * (s : ℚ) - 2 - 2 * m)) =
      ((∏ m ∈ Finset.Icc 1 i,
        (Fintype.card (CoefIdxD n d) + 2 * s - 2 - 2 * m) : ℕ) : ℚ) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro m hm
    obtain ⟨hm1, hmi⟩ := Finset.mem_Icc.mp hm
    have hsub : 2 * m ≤ Fintype.card (CoefIdxD n d) + 2 * s - 2 := by omega
    have hsub' : 2 ≤ Fintype.card (CoefIdxD n d) + 2 * s := by omega
    rw [Nat.cast_sub hsub, Nat.cast_sub hsub']
    simp [DQ]
  rw [hp]
  have hnum : (-1 : ℚ) ^ i *
      ((s.choose (2 * i) * (2 * i - 1).doubleFactorial : ℕ) : ℚ) =
      (((-1 : ℤ) ^ i * (s.choose (2 * i) * (2 * i - 1).doubleFactorial : ℕ) : ℤ) : ℚ) := by
    push_cast; rfl
  rw [hnum]
  exact rat_int_div_den_dvd _ _

private lemma muQ_den_le (hn : 1 ≤ n) (s i k : ℕ) (hi : 2 * i ≤ s) (hs : s ≤ k) :
    (muQ n d s i).den ≤ (Fintype.card (CoefIdxD n d) + 2 * k) ^ i := by
  have hd := muQ_den_dvd (n := n) (d := d) s i hi
  let a : Fin n := ⟨0, by omega⟩
  let : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, a)⟩⟩
  have hc : 0 < Fintype.card (CoefIdxD n d) := Fintype.card_pos
  have hpos : 0 < ∏ m ∈ Finset.Icc 1 i,
      (Fintype.card (CoefIdxD n d) + 2 * s - 2 - 2 * m) := by
    apply Finset.prod_pos
    intro m hm
    obtain ⟨hm1, hmi⟩ := Finset.mem_Icc.mp hm
    omega
  calc
    _ ≤ _ := Nat.le_of_dvd hpos hd
    _ ≤ ∏ _m ∈ Finset.Icc 1 i, (Fintype.card (CoefIdxD n d) + 2 * k) := by
      apply Finset.prod_le_prod
      intro m hm
      omega
    _ = _ := by simp

private lemma trHKQ_bounds {s : ℕ} (K : Finset (Multiset (Mono n d))) (l i : ℕ)
    (w : Fin (s - 2 * i) → Mono n d) :
    0 ≤ trL i (HKQ K l) w ∧
      trL i (HKQ K l) w ≤ (Fintype.card (Mono n d) : ℚ) ^ (l + i) := by
  classical
  have hb (v : Fin s → Mono n d) : 0 ≤ HKQ K l v ∧
      HKQ K l v ≤ (Fintype.card (Mono n d) : ℚ) ^ l := by
    unfold HKQ
    split_ifs
    · exact const_HQ_bounds l v
    · constructor <;> positivity
  unfold trL
  constructor
  · exact Finset.sum_nonneg (fun c _ => (hb _).1)
  · calc
      _ ≤ ∑ _c : Fin i → Mono n d, (Fintype.card (Mono n d) : ℚ) ^ l :=
        Finset.sum_le_sum (fun c _ => (hb _).2)
      _ = _ := by simp [pow_add]; ring

private lemma kapQ_abs_le (hn : 1 ≤ n) (j l : ℕ) :
    |kapQ n d j l| ≤ (j.factorial : ℚ) := by
  let a : Fin n := ⟨0, by omega⟩
  let : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, a)⟩⟩
  have hc : (1 : ℚ) ≤ DQ n d := by
    unfold DQ
    exact_mod_cast Fintype.card_pos (α := CoefIdxD n d)
  have hp : (1 : ℚ) ≤ ∏ i ∈ Finset.range l,
      (DQ n d + 2 * ((j - 2 * l : ℕ) : ℚ) + 2 * i) := by
    apply Finset.one_le_prod₀
    intro i hi
    have h1 : (0 : ℚ) ≤ 2 * ((j - 2 * l : ℕ) : ℚ) := by positivity
    have h2 : (0 : ℚ) ≤ 2 * i := by positivity
    linarith
  unfold kapQ
  rw [abs_of_nonneg (div_nonneg (cQ_bounds j l).1 (by linarith))]
  exact (div_le_self (cQ_bounds j l).1 hp).trans (cQ_bounds j l).2

private lemma muQ_abs_le (hn : 1 ≤ n) (s i : ℕ) (hi : 2 * i ≤ s) :
    |muQ n d s i| ≤ (s.factorial : ℚ) := by
  let a : Fin n := ⟨0, by omega⟩
  let : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, a)⟩⟩
  have hc : (1 : ℚ) ≤ DQ n d := by
    unfold DQ
    exact_mod_cast Fintype.card_pos (α := CoefIdxD n d)
  have hp : (1 : ℚ) ≤ ∏ m ∈ Finset.Icc 1 i, (DQ n d + 2 * (s : ℚ) - 2 - 2 * m) := by
    apply Finset.one_le_prod₀
    intro m hm
    obtain ⟨hm1, hmi⟩ := Finset.mem_Icc.mp hm
    have hsm : 2 + 2 * m ≤ 2 * s := by omega
    have hh : (2 : ℚ) + 2 * m ≤ 2 * s := by exact_mod_cast hsm
    linarith
  unfold muQ
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (cQ_bounds s i).1, abs_of_nonneg (by linarith : (0 : ℚ) ≤ _)]
  exact (div_le_self (cQ_bounds s i).1 hp).trans (cQ_bounds s i).2

private lemma orbSize_le (q : Multiset (Mono n d)) : orbSize q ≤ q.card.factorial := by
  classical
  unfold orbSize
  exact Nat.div_le_self _ _

private lemma mul_den_le (a b : ℚ) : (a * b).den ≤ a.den * b.den :=
  Nat.le_of_dvd (by positivity) (Rat.mul_den_dvd a b)

private lemma rat_num_le (q : ℚ) (A B : ℕ) (hden : q.den ≤ A) (hval : |q| ≤ (B : ℚ)) :
    q.num.natAbs ≤ A * B := by
  have he : (q.num.natAbs : ℚ) = |q| * (q.den : ℚ) := by
    have hq := q.num_div_den
    have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
    have hh := congrArg abs hq
    rw [abs_div, abs_of_pos hd, ← Int.cast_abs, ← Nat.cast_natAbs] at hh
    exact (div_eq_iff hd.ne').mp hh
  have hd' : (q.den : ℚ) ≤ A := by exact_mod_cast hden
  have h : (q.num.natAbs : ℚ) ≤ (A * B : ℕ) := by
    rw [he, Nat.cast_mul, mul_comm (A : ℚ)]
    exact mul_le_mul hval hd' (by positivity) (by positivity)
  exact_mod_cast h

private lemma key_constraints (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (key : Key n d) (hk : key ∈ keys k K) :
    key.1 ≤ k ∧ 2 * key.2.1 ≤ key.1 ∧ 2 * key.2.2.1 ≤ key.1 - 2 * key.2.1 ∧
      key.2.2.2.card = key.1 - 2 * key.2.1 - 2 * key.2.2.1 := by
  classical
  unfold keys at hk
  rcases List.mem_append.mp hk with hk | hk
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
    have hj' := Finset.mem_filter.mp (Finset.mem_toList.mp hj)
    obtain ⟨r, hr⟩ := hj'.2
    have hjk := (Finset.mem_Icc.mp hj'.1).2
    simp only [Multiset.card_zero]
    omega
  · obtain ⟨jl, hjl, hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨i, hi, hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hk
    have hl := Finset.mem_filter.mp (Finset.mem_toList.mp hjl)
    have hj := Finset.mem_product.mp hl.1
    have hi' := List.mem_range.mp hi
    have hcard := q.2
    simp only
    exact ⟨(Finset.mem_Icc.mp hj.1).2, by omega, by omega, hcard⟩

private lemma key_weight_bounds (hn : 1 ≤ n) (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (key : Key n d) (hk : key ∈ keys k K) :
    (wKey K key).den ≤ rhoNat n (k * d) * (Fintype.card (CoefIdxD n d) + 2 * k) ^ (2 * k) ∧
      |wKey K key| ≤ ((k.factorial ^ 3 * Fintype.card (Mono n d) ^ k : ℕ) : ℚ) := by
  classical
  obtain ⟨hj, hl, hi, hcard⟩ := key_constraints k K key hk
  let j := key.1
  let l := key.2.1
  let i := key.2.2.1
  let s := j - 2 * l
  let A := Fintype.card (CoefIdxD n d) + 2 * k
  let N := Fintype.card (Mono n d)
  have hc : 1 ≤ Fintype.card (CoefIdxD n d) := by
    let a : Fin n := ⟨0, by omega⟩
    let : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, a)⟩⟩
    exact Fintype.card_pos
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hN : 1 ≤ N := Fintype.card_pos
  have hNq : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have hfk : (1 : ℚ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hpowN : (1 : ℚ) ≤ (N : ℚ) ^ k := one_le_pow₀ hNq
  have hjf : (j.factorial : ℚ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hj
  have hsf : (s.factorial : ℚ) ≤ k.factorial := by
    exact_mod_cast Nat.factorial_le (show s ≤ k by dsimp [s, j, l]; omega)
  have hqf : (orbSize key.2.2.2 : ℚ) ≤ k.factorial := by
    exact_mod_cast (orbSize_le key.2.2.2).trans
      (Nat.factorial_le (by rw [hcard]; omega))
  have hkap : (kapQ n d j l).den ≤ A ^ l := kapQ_den_le hn j l k hl hj
  have habs : |kapQ n d j l| ≤ k.factorial := (kapQ_abs_le hn j l).trans hjf
  unfold wKey
  split_ifs with he
  · have hHQ := HQ_den_dvd (n := n) (d := d) l k
      (s := j - 2 * l) (by dsimp [j, l]; omega) (fun _ => default)
    have hden : (HQ (n := n) (d := d) (s := j - 2 * l) l (fun _ => default)).den ≤
        rhoNat n (k * d) := Nat.le_of_dvd (rhoNat_pos hn _) hHQ
    constructor
    · calc
        _ ≤ (kapQ n d j l).den * (HQ (n := n) (d := d) (s := j - 2 * l) l (fun _ => default)).den :=
          mul_den_le _ _
        _ ≤ A ^ l * rhoNat n (k * d) := Nat.mul_le_mul hkap hden
        _ ≤ A ^ (2 * k) * rhoNat n (k * d) := Nat.mul_le_mul_right _
          (Nat.pow_le_pow_right hA (by dsimp [l]; omega))
        _ = _ := by ring
    · have hH := const_HQ_bounds (n := n) (d := d) (s := j - 2 * l) l (fun _ => default)
      have hHabs : |HQ (n := n) (d := d) (s := j - 2 * l) l (fun _ => default)| ≤ (N : ℚ) ^ k := by
        rw [abs_of_nonneg hH.1]
        exact hH.2.trans (pow_le_pow_right₀ hNq (by dsimp [l]; omega))
      rw [abs_mul]
      calc
        _ ≤ (k.factorial : ℚ) * (N : ℚ) ^ k :=
          mul_le_mul habs hHabs (abs_nonneg _) (by positivity)
        _ ≤ (k.factorial : ℚ) ^ 3 * (N : ℚ) ^ k := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith [sq_nonneg ((k.factorial : ℚ) - 1)]
        _ = _ := by push_cast; rfl
  · have hs : s + 2 * l ≤ k := by dsimp [s, j, l]; omega
    have hmu : (muQ n d s i).den ≤ A ^ i := muQ_den_le hn s i k hi (by dsimp [s, j, l]; omega)
    have hH := trHKQ_den_dvd (K j l) l i k hs (wordOf _ key.2.2.2)
    have hHden : (trL i (HKQ (s := s) (K j l) l) (wordOf _ key.2.2.2)).den ≤ rhoNat n (k * d) :=
      Nat.le_of_dvd (rhoNat_pos hn _) hH
    constructor
    · calc
        _ ≤ ((kapQ n d j l * muQ n d s i) * (orbSize key.2.2.2 : ℚ)).den *
            (trL i (HKQ (s := s) (K j l) l) (wordOf _ key.2.2.2)).den := mul_den_le _ _
        _ ≤ ((kapQ n d j l).den * (muQ n d s i).den * 1) * rhoNat n (k * d) := by
          apply Nat.mul_le_mul _ hHden
          exact (mul_den_le _ _).trans (by simpa using mul_den_le (kapQ n d j l) (muQ n d s i))
        _ ≤ (A ^ l * A ^ i * 1) * rhoNat n (k * d) := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul hkap hmu))
        _ ≤ A ^ (2 * k) * rhoNat n (k * d) := by
          rw [mul_one, ← pow_add]
          apply Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hA _)
          dsimp [l, i, s] at *; omega
        _ = _ := by ring
    · have hHbounds := trHKQ_bounds (s := s) (K j l) l i (wordOf _ key.2.2.2)
      have hHabs : |trL i (HKQ (s := s) (K j l) l) (wordOf _ key.2.2.2)| ≤ (N : ℚ) ^ k := by
        rw [abs_of_nonneg hHbounds.1]
        exact hHbounds.2.trans (pow_le_pow_right₀ hNq (by dsimp [l, i, s] at *; omega))
      have hmuabs : |muQ n d s i| ≤ k.factorial := (muQ_abs_le hn s i hi).trans hsf
      simp only [abs_mul, abs_of_nonneg (show (0 : ℚ) ≤ (orbSize key.2.2.2 : ℚ) by positivity)]
      calc
        _ ≤ ((k.factorial : ℚ) * k.factorial * k.factorial) * (N : ℚ) ^ k := by
          apply mul_le_mul _ hHabs (abs_nonneg _) (by positivity)
          exact mul_le_mul (mul_le_mul habs hmuabs (abs_nonneg _) (by positivity)) hqf (by positivity) (by positivity)
        _ = _ := by push_cast; ring

private def Allowed {ι : Type} (Q : ℚ → Prop) (a : Arg ι) : Prop :=
  ∀ q, a = .cst q → q = 0 ∨ q = 1 ∨ Q q

private def AllowedProg {ι κ : Type} (Q : ℚ → Prop) (p : Prog ι κ) : Prop :=
  (∀ I ∈ p.body, Allowed Q I.a ∧ Allowed Q I.b) ∧ ∀ o, Allowed Q (p.out o)

private lemma light_allowed {ι κ : Type} (Q : ℚ → Prop) (p : Prog ι κ) (hp : LightProg p) :
    AllowedProg Q p := by
  have ha : ∀ a : Arg ι, Light a → Allowed Q a := by
    intro a h q hq
    rcases h q hq with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  exact ⟨fun I hI => ⟨ha _ (hp.1 I hI).1, ha _ (hp.1 I hI).2⟩, fun o => ha _ (hp.2 o)⟩

private lemma allowed_inp {ι : Type} (Q : ℚ → Prop) (i : ι) : Allowed Q (.inp i) := by
  intro q h; cases h

private lemma allowed_reg {ι : Type} (Q : ℚ → Prop) (r : ℕ) : Allowed Q (Arg.reg (ι := ι) r) := by
  intro q h; cases h

private lemma allowed_zero {ι : Type} (Q : ℚ → Prop) : Allowed Q (Arg.cst (ι := ι) 0) := by
  intro q h; cases h; exact Or.inl rfl

private lemma allowed_rename {ι ι' : Type} (Q : ℚ → Prop) (a : Arg ι)
    (h : Allowed Q a) (σ : ι → ι') : Allowed Q (a.rename σ) := by
  cases a with
  | inp i => exact allowed_inp _ _
  | reg r => exact allowed_reg _ _
  | cst q => intro r hr; cases hr; exact h q rfl

private lemma allowed_clamp {ι : Type} (Q : ℚ → Prop) (a : Arg ι)
    (h : Allowed Q a) (s : ℕ) : Allowed Q (a.clamp s) := by
  cases a with
  | inp i => exact allowed_inp _ _
  | reg r => simp only [Arg.clamp]; split <;> first | exact allowed_reg _ _ | exact allowed_zero _
  | cst q => exact h

private lemma allowed_subst {ι ι' : Type} (Q : ℚ → Prop) (a : Arg ι) (h : Allowed Q a)
    (σ : ι → Arg ι') (hσ : ∀ i, Allowed Q (σ i)) (s len : ℕ) :
    Allowed Q (a.subst σ s len) := by
  cases a with
  | inp i => exact hσ i
  | reg r => simp only [Arg.subst]; split <;> first | exact allowed_reg _ _ | exact allowed_zero _
  | cst q => intro r hr; cases hr; exact h q rfl

private lemma allowed_bind {ι κ ν : Type} (Q : ℚ → Prop)
    (p : Prog ι κ) (q : Prog (ι ⊕ κ) ν) (hp : AllowedProg Q p) (hq : AllowedProg Q q) :
    AllowedProg Q (p.bind q) := by
  let σ : ι ⊕ κ → Arg ι := Sum.elim Arg.inp (fun o => (p.out o).clamp p.body.length)
  have hs : ∀ i, Allowed Q (σ i) := by
    intro i; cases i with
    | inl i => exact allowed_inp _ _
    | inr o => exact allowed_clamp _ _ (hp.2 o) _
  constructor
  · intro I hI
    simp only [Prog.bind, List.mem_append, List.mem_map] at hI
    rcases hI with hI | ⟨J, hJ, rfl⟩
    · exact hp.1 I hI
    · exact ⟨allowed_subst _ _ (hq.1 J hJ).1 σ hs _ _,
        allowed_subst _ _ (hq.1 J hJ).2 σ hs _ _⟩
  · intro o
    exact allowed_subst _ _ (hq.2 o) σ hs _ _

private lemma allowed_par {ι κ : Type} [DecidableEq κ] (Q : ℚ → Prop)
    (p : κ → Prog ι Unit) (l : List κ) (hp : ∀ o ∈ l, AllowedProg Q (p o)) :
    AllowedProg Q (Prog.par p l) := by
  induction l with
  | nil => exact ⟨by simp [Prog.par, Prog.ofArgs], fun _ => allowed_zero _⟩
  | cons o l ih =>
    apply allowed_bind _ _ _ (hp o (by simp))
    have ht := ih (fun a ha => hp a (by simp [ha]))
    constructor
    · intro I hI
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
      exact ⟨allowed_rename _ _ (ht.1 J hJ).1 _, allowed_rename _ _ (ht.1 J hJ).2 _⟩
    · intro j
      simp only
      split
      · exact allowed_inp _ _
      · exact allowed_rename _ _ (ht.2 j) _

private lemma light_mapIn {ι ι' κ : Type} (σ : ι → ι') (p : Prog ι κ) (hp : LightProg p) :
    LightProg (p.mapIn σ) := by
  constructor
  · intro I hI
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
    exact ⟨light_rename _ (hp.1 J hJ).1 _, light_rename _ (hp.1 J hJ).2 _⟩
  · intro o; exact light_rename _ (hp.2 o) _

private lemma light_sumArgs {ι : Type} (l : List (Arg ι)) (hl : ∀ a ∈ l, Light a) :
    LightProg (Prog.sumArgs l) := by
  induction l with
  | nil => exact light_ofArgs _ (fun _ => light_zero)
  | cons a l ih =>
    cases l with
    | nil => exact light_ofArgs _ (fun _ => hl a (by simp))
    | cons b l =>
      exact light_bind _ _ (ih (fun c hc => hl c (by simp [hc])))
        (light_op _ _ _ (light_rename _ (hl a (by simp)) _) (light_inp _))

private lemma light_sumProd {ι : Type} (l : List (Arg ι × Arg ι))
    (hl : ∀ a ∈ l, Light a.1 ∧ Light a.2) : LightProg (Prog.sumProd l) := by
  unfold Prog.sumProd
  apply light_bind
  · apply light_par
    intro j hj
    have h := hl (l.get j) (List.get_mem _ _)
    exact light_op _ _ _ h.1 h.2
  · apply light_sumArgs
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    exact light_inp _

private lemma light_contract {ι : Type} (a : ℕ)
    (A : (Fin a → Fin n) → Arg ι) (v : Fin a → Fin n → Arg ι)
    (hA : ∀ w, Light (A w)) (hv : ∀ t c, Light (v t c)) :
    LightProg (contractProg a A v) := by
  induction a generalizing ι with
  | zero => exact light_ofArgs _ (fun _ => hA _)
  | succ a ih =>
    unfold contractProg
    apply light_bind
    · apply light_par
      intro w hw
      apply light_sumProd
      intro pair hpair
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hpair
      exact ⟨hA _, hv _ _⟩
    · apply ih
      · intro w; exact light_inp _
      · intro t c; exact light_rename _ (hv _ _) _

private lemma light_trProg (n d k : ℕ) : LightProg (trProg n d k) := by
  unfold trProg
  apply light_par
  intro x hx
  unfold trSlotProg
  apply light_sumArgs
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  exact light_inp _

private lemma light_trArg (j m : ℕ) (w : Fin (j - 2 * m) → Fin n) :
    Light (trArg (d := d) (k := k) j m w) := by
  unfold trArg
  split <;> exact light_inp _

private lemma program_constants (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) :
    AllowedProg (fun q => ∃ key ∈ keys k K, q = wKey K key) (gProgL n d k K) := by
  classical
  let Q : ℚ → Prop := fun q => ∃ key ∈ keys k K, q = wKey K key
  unfold gProgL
  apply allowed_bind
  · exact light_allowed Q _ (light_trProg n d k)
  · apply allowed_bind
    · apply allowed_par
      intro key hk
      unfold keyProg
      apply allowed_bind
      · apply light_allowed
        apply light_contract
        · intro w; exact light_trArg _ _ _
        · intro t c; exact light_inp _
      · constructor
        · intro I hI
          simp only [Prog.op1, List.mem_singleton] at hI
          subst I
          refine ⟨allowed_inp _ _, ?_⟩
          intro q hq
          cases hq
          exact Or.inr (Or.inr ⟨key, hk, rfl⟩)
        · intro o; exact allowed_reg _ _
    · apply light_allowed
      apply light_sumArgs
      intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · subst a; exact light_inp _
      · obtain ⟨key, hk, rfl⟩ := List.mem_map.mp ha
        exact light_inp _

private lemma heavy_weight (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (q : ℚ) (hq : q ∈ heavyConsts (gProgL n d k K)) :
    ∃ key ∈ keys k K, q = wKey K key := by
  classical
  let p := gProgL n d k K
  have hp := program_constants k K
  change q ∈ (args p).filterMap collect at hq
  obtain ⟨a, ha, hq⟩ := List.mem_filterMap.mp hq
  cases a with
  | inp i => simp [collect] at hq
  | reg r => simp [collect] at hq
  | cst r =>
    by_cases hr : r = 0 ∨ r = 1
    · simp [collect, hr] at hq
    · have he : r = q := by simpa [collect, hr] using hq
      subst r
      have hh : Allowed (fun q => ∃ key ∈ keys k K, q = wKey K key) (Arg.cst (ι := In41 n d k) q) := by
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨I, hI, ha⟩ := List.mem_flatMap.mp ha
          rcases List.mem_cons.mp ha with ha | ha
          · rw [ha]; exact (hp.1 I hI).1
          · have h : Arg.cst q = I.b := by simpa using ha
            rw [h]; exact (hp.1 I hI).2
        · obtain ⟨o, ho, he⟩ := List.mem_map.mp ha
          rw [← he]; exact hp.2 o
      rcases hh q rfl with h | h | h
      · exact (hr (Or.inl h)).elim
      · exact (hr (Or.inr h)).elim
      · exact h

private lemma heights_of_le (q : ℚ) (hnum : q.num.natAbs ≤ Hgt n d k)
    (hden : q.den ≤ Hgt n d k) :
    q.num.natAbs < 2 ^ bQ n d k ∧ q.den < 2 ^ bQ n d k := by
  have h : Hgt n d k < 2 ^ bQ n d k := Nat.lt_pow_succ_log_self (by decide) _
  exact ⟨hnum.trans_lt h, hden.trans_lt h⟩

/-- **The heights of the moment constants**: every heavy constant of the branch has `|num|, den < 2^{b_Q}`. -/
theorem gProgL_heights (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (hK : ∀ jl ∈ levels k, ∀ o ∈ K jl.1 jl.2, Multiset.card o = jl.1 - 2 * jl.2) :
    ∀ q ∈ heavyConsts (gProgL n d k K), q.num.natAbs < 2 ^ bQ n d k ∧ q.den < 2 ^ bQ n d k := by
  clear hk hK
  intro q hq
  obtain ⟨key, hkey, rfl⟩ := heavy_weight k K q hq
  obtain ⟨hden, hval⟩ := key_weight_bounds hn k K key hkey
  let A := rhoNat n (k * d) * (Fintype.card (CoefIdxD n d) + 2 * k) ^ (2 * k)
  let B := k.factorial ^ 3 * Fintype.card (Mono n d) ^ k
  have hB : 0 < B := by
    have hN : 0 < Fintype.card (Mono n d) := Fintype.card_pos
    dsimp [B]
    positivity
  have hnum : (wKey K key).num.natAbs ≤ A * B := rat_num_le _ A B hden hval
  have hgt : Hgt n d k = A * B * (d + 1) ^ k := by
    dsimp [Hgt, A, B, rhoNat]
    ring
  have hAB : A * B ≤ Hgt n d k := by
    rw [hgt]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  apply heights_of_le
  · exact hnum.trans hAB
  · exact hden.trans ((Nat.le_mul_of_pos_right _ hB).trans hAB)


end BstLean.Part41
