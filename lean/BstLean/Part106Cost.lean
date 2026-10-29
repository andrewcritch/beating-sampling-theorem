import BstLean.Part106Defs

/-!
# Part 106, item 1: the program `g` and its cost

Role: `delegations/statements/p106-spec.md`, item 1. Cost model: `SProg` of Part 105 (the four
arithmetic operations and the square root, one unit each; reading an input or a rational constant
is free).

* `gProg r n dA dF k`: the program. Inputs (`GIn`): the coefficients of degree `0` and `1` of `W`
  (`w0 a`, `w1 a j`), the noise level `τ`, the coefficients of `A` and of `F`, and `k` blocks
  `(us i, gs i)`. The input type has no coefficient of `W` of degree `≥ 2`.
* `gProg_eval`, `gProg_eval_gVal`: its value is `gVal` of `Part106Defs`.
* `gProg_cost`: its cost is at most `gCost k r n dA dF`.
* `sample_lower`: every program of the model that computes one sample of `s_B` for all inputs has
  `D_W ≤ 2·cost + 1`, `D_W` the number of coefficients of `W` (a reading bound).
* `gCost_lt_lower`, `gProg_cost_lt_sampleProg'`, `gCost_lt_sampleCost'`, `gCost_lt_top`,
  `gProg_cost_lt_any`: the comparisons at `r = 2`, `d_A, d_F ∈ {3, 4}`, `n ≥ 4096`, `k ≤ n²`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part106

open BstLean.Cost BstLean.Part105

noncomputable section

/-! ## A combinator: the sum of the outputs of a list of programs -/

section sumList

variable {ι κ : Type}

/-- Run the programs `p j`, `j ∈ l`, and add their outputs (`length − 1` additions). -/
def sumList (p : κ → SProg ι Unit) : List κ → SProg ι Unit
  | [] => ⟨[], fun _ => .cst 0⟩
  | [j] => p j
  | j :: j' :: l =>
      (sumList p (j' :: l)).bind
        (((p j).mapIn Sum.inl).bind
          (SProg.ofProg (Prog.op1 .add (.inp (.inl (.inr ()))) (.inp (.inr ())))))

theorem sumList_eval (p : κ → SProg ι Unit) (l : List κ) (v : ι → ℝ) (u : Unit) :
    (sumList p l).eval v u = (l.map fun j => (p j).eval v ()).sum := by
  induction l with
  | nil => simp [sumList, SProg.eval, Arg.eval]
  | cons j l ih =>
    cases l with
    | nil => simp [sumList]
    | cons j' l =>
      simp only [sumList, SProg.eval_bind, SProg.eval_ofProg, eval_op1, Op.eval, Arg.eval,
        Sum.elim_inl, Sum.elim_inr, SProg.eval_mapIn]
      rw [ih, List.map_cons (a := j), List.sum_cons, add_comm]
      rfl

theorem sumList_cost (p : κ → SProg ι Unit) (l : List κ) :
    (sumList p l).cost = (l.map fun j => (p j).cost).sum + (l.length - 1) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    cases l with
    | nil => simp [sumList]
    | cons j' l =>
      simp only [sumList, SProg.cost_bind, SProg.cost_ofProg, cost_op1, SProg.cost_mapIn, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

end sumList

/-! ## The inputs of `g` -/

/-- The inputs of the program `g`: the coefficients of degree `0` and `1` of `W`, the noise level
`τ`, the coefficients of `A`, the coefficients of `F`, and the `k` blocks of random inputs. -/
abbrev GIn (r n dA dF k : ℕ) : Type :=
  (Fin n ⊕ (Fin n × Fin (r * n))) ⊕ Unit ⊕ CoefIdx n n dA ⊕ CoefIdx n 1 dF ⊕
    (Fin k × Fin (r * n)) ⊕ (Fin k × Fin n)

variable {r n dA dF k : ℕ}

/-- The inputs as one valuation. -/
def gInVal (w0 : Fin n → ℝ) (w1 : Fin n → Fin (r * n) → ℝ) (τ : ℝ) (A : CoefIdx n n dA → ℝ)
    (F : CoefIdx n 1 dF → ℝ) (us : Fin k → Fin (r * n) → ℝ) (gs : Fin k → Fin n → ℝ) :
    GIn r n dA dF k → ℝ :=
  Sum.elim (Sum.elim w0 (fun p => w1 p.1 p.2))
    (Sum.elim (fun _ => τ) (Sum.elim A (Sum.elim F
      (Sum.elim (fun p => us p.1 p.2) (fun p => gs p.1 p.2)))))

/-- The pairs of the sum of products `Σ_j w1_{a j} u_{i j} + τ g_{i a}`. -/
def yPairs (r n dA dF k : ℕ) (i : Fin k) (a : Fin n) :
    List (Arg (GIn r n dA dF k) × Arg (GIn r n dA dF k)) :=
  (List.finRange (r * n)).map (fun j =>
      (Arg.inp (Sum.inl (Sum.inr (a, j))),
        Arg.inp (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))))))) ++
    [(Arg.inp (Sum.inr (Sum.inl ())),
      Arg.inp (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, a)))))))]

/-- `y = W_0 + W_1 u_i + τ g_i`: `2rn + 2` operations for each coordinate. -/
def yProg (r n dA dF k : ℕ) (i : Fin k) : Prog (GIn r n dA dF k) (Fin n) :=
  Prog.par (fun a : Fin n =>
      (Prog.sumProd (yPairs r n dA dF k i a)).bind
        (Prog.op1 .add (.inp (.inl (.inl (.inl a)))) (.inp (.inr ()))))
    (List.finRange n)

theorem yProg_eval (w0 : Fin n → ℝ) (w1 : Fin n → Fin (r * n) → ℝ) (τ : ℝ)
    (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) (us : Fin k → Fin (r * n) → ℝ)
    (gs : Fin k → Fin n → ℝ) (i : Fin k) (a : Fin n) :
    (yProg r n dA dF k i).eval (gInVal w0 w1 τ A F us gs) a =
      w0 a + ∑ j, w1 a j * us i j + τ * gs i a := by
  rw [yProg, eval_par_mem _ _ _ _ (List.mem_finRange a), eval_bind, eval_op1]
  simp only [Op.eval, Arg.eval, Sum.elim_inl, Sum.elim_inr, eval_sumProd, yPairs,
    List.map_append, List.map_map, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, gInVal, Fin.sum_univ_def, Function.comp_def]
  ring

theorem yProg_cost (r n dA dF k : ℕ) (i : Fin k) :
    (yProg r n dA dF k i).cost = n * (2 * r * n + 2) := by
  simp only [yProg, cost_par, cost_bind, cost_sumProd, cost_op1, yPairs, List.length_append,
    List.length_map, List.length_finRange, List.length_cons, List.length_nil, List.map_const',
    List.sum_replicate, smul_eq_mul]
  have : 2 * (r * n + (0 + 1)) - 1 + 1 = 2 * r * n + 2 := by
    have : 2 * (r * n + (0 + 1)) = 2 * r * n + 2 := by ring
    omega
  rw [this]

/-- One sample of the stand-in and the value `F(A(x_i))`. -/
def sampleG (r n dA dF k : ℕ) (i : Fin k) : SProg (GIn r n dA dF k) Unit :=
  (((SProg.ofProg (yProg r n dA dF k i)).bind ((rescaleProg n).mapIn Sum.inr)).bind
      (SProg.ofProg ((evalProg n n dA).mapIn
        (Sum.elim Sum.inr (fun c => Sum.inl (Sum.inr (Sum.inr (Sum.inl c)))))))).bind
    (SProg.ofProg ((hornerProg n 1 dF 0).mapIn
      (Sum.elim Sum.inr (fun c => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl c))))))))

theorem sampleG_eval (w0 : Fin n → ℝ) (w1 : Fin n → Fin (r * n) → ℝ) (τ : ℝ)
    (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) (us : Fin k → Fin (r * n) → ℝ)
    (gs : Fin k → Fin n → ℝ) (i : Fin k) (u : Unit) :
    (sampleG r n dA dF k i).eval (gInVal w0 w1 τ A F us gs) u =
      bwEval F (bwEval A (sphProj (fun a => w0 a + ∑ j, w1 a j * us i j + τ * gs i a))) 0 := by
  set v := gInVal w0 w1 τ A F us gs with hv
  set y : Fin n → ℝ := fun a => w0 a + ∑ j, w1 a j * us i j + τ * gs i a with hy
  have h1 : ((SProg.ofProg (yProg r n dA dF k i)).bind ((rescaleProg n).mapIn Sum.inr)).eval v =
      sphProj y := by
    funext a
    rw [SProg.eval_bind, SProg.eval_mapIn]
    have : (Sum.elim v ((SProg.ofProg (yProg r n dA dF k i)).eval v) ∘ Sum.inr) = y := by
      funext b
      simp only [Function.comp, Sum.elim_inr, SProg.eval_ofProg]
      exact yProg_eval w0 w1 τ A F us gs i b
    rw [this, rescaleProg_eval]
  have h2 : (((SProg.ofProg (yProg r n dA dF k i)).bind ((rescaleProg n).mapIn Sum.inr)).bind
      (SProg.ofProg ((evalProg n n dA).mapIn
        (Sum.elim Sum.inr (fun c => Sum.inl (Sum.inr (Sum.inr (Sum.inl c)))))))).eval v =
      bwEval A (sphProj y) := by
    funext a
    rw [SProg.eval_bind, SProg.eval_ofProg, eval_mapIn, h1]
    have : (Sum.elim v (sphProj y) ∘
        (Sum.elim Sum.inr (fun c => Sum.inl (Sum.inr (Sum.inr (Sum.inl c)))))) =
        Sum.elim (sphProj y) A := by
      funext j
      cases j <;> rfl
    rw [this, evalProg_eval]
  cases u
  rw [sampleG, SProg.eval_bind, SProg.eval_ofProg, eval_mapIn, h2]
  have : (Sum.elim v (bwEval A (sphProj y)) ∘
      (Sum.elim Sum.inr (fun c => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl c))))))) =
      Sum.elim (bwEval A (sphProj y)) F := by
    funext j
    cases j <;> rfl
  rw [this, hornerProg_eval]

/-- The cost bound of one sample of the stand-in with `F(A(x_i))`. -/
def gSampleCost (r n dA dF : ℕ) : ℕ :=
  2 * r * n ^ 2 + 5 * n + 1 + Ecost n n dA + (2 * (n + dF).choose dF - 2)

theorem sampleG_cost (r n dA dF k : ℕ) (i : Fin k) :
    (sampleG r n dA dF k i).cost ≤ gSampleCost r n dA dF := by
  simp only [sampleG, SProg.cost_bind, SProg.cost_ofProg, SProg.cost_mapIn, cost_mapIn,
    yProg_cost, gSampleCost]
  have h2 := rescaleProg_cost n
  have h3 := evalProg_cost n n dA
  have h4 := hornerProg_cost n 1 dF 0
  have : n * (2 * r * n + 2) = 2 * r * n ^ 2 + 2 * n := by ring
  omega

/-! ## The program `g` -/

/-- **The program `g`**: the mean over the `k` blocks of `F(A(x_i))`, `x_i = y_i/|y_i|`,
`y_i = W_0 + W_1 u_i + τ g_i`. (For `k = 0` the program is empty and returns `0`.) -/
def gProg (r n dA dF k : ℕ) : SProg (GIn r n dA dF k) Unit :=
  if k = 0 then ⟨[], fun _ => .cst 0⟩ else
    (sumList (sampleG r n dA dF k) (List.finRange k)).bind
      (SProg.ofProg (Prog.op1 .div (.inp (.inr ())) (.cst (k : ℚ))))

/-- **The value of `g`.** -/
theorem gProg_eval (w0 : Fin n → ℝ) (w1 : Fin n → Fin (r * n) → ℝ) (τ : ℝ)
    (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) (us : Fin k → Fin (r * n) → ℝ)
    (gs : Fin k → Fin n → ℝ) :
    (gProg r n dA dF k).eval (gInVal w0 w1 τ A F us gs) () =
      (∑ i, bwEval F (bwEval A
        (sphProj (fun a => w0 a + ∑ j, w1 a j * us i j + τ * gs i a))) 0) / (k : ℝ) := by
  by_cases hk : k = 0
  · subst hk
    simp [gProg, SProg.eval, Arg.eval]
  · simp only [gProg, hk, ite_false, SProg.eval_bind, SProg.eval_ofProg, eval_op1, Op.eval,
      Arg.eval, Sum.elim_inr, sumList_eval, sampleG_eval, Rat.cast_natCast, Fin.sum_univ_def]

/-- The cost bound of `g`: `k` samples, `k − 1` additions and one division. -/
def gCost (k r n dA dF : ℕ) : ℕ :=
  k * (2 * r * n ^ 2 + 5 * n + 1 + Ecost n n dA + (2 * (n + dF).choose dF - 2)) + k

/-- **The cost of `g`.** -/
theorem gProg_cost (r n dA dF k : ℕ) : (gProg r n dA dF k).cost ≤ gCost k r n dA dF := by
  by_cases hk : k = 0
  · subst hk
    simp [gProg, SProg.cost]
  · simp only [gProg, hk, ite_false, SProg.cost_bind, SProg.cost_ofProg, cost_op1, sumList_cost,
      List.length_finRange, gCost]
    have h : ((List.finRange k).map fun j => (sampleG r n dA dF k j).cost).sum ≤
        k * gSampleCost r n dA dF := by
      have := List.sum_le_length_nsmul ((List.finRange k).map fun j => (sampleG r n dA dF k j).cost)
        (gSampleCost r n dA dF) (by
          intro x hx
          obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
          exact sampleG_cost r n dA dF k j)
      simpa using this
    unfold gSampleCost at h
    omega

/-! ## The link to `gVal` -/

theorem monoVal_mono1 {N d : ℕ} (hd : 1 ≤ d) (x : Fin N → ℝ) (j : Fin N) :
    monoVal x (mono1 N d hd j) = x j := by
  simp [monoVal, mono1]

theorem eq_mono1 {N d : ℕ} (hd : 1 ≤ d) (m : MonoIdx N d) (h : m.1.val = 1) :
    ∃ j, m = mono1 N d hd j := by
  obtain ⟨⟨j, hj⟩, s⟩ := m
  simp only at h
  subst h
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp s.2
  refine ⟨a, ?_⟩
  simp only [mono1]
  congr 1
  exact Subtype.ext ha

/-- The terms of degree `0` and `1` of a polynomial map. -/
theorem lowEval {N n d : ℕ} (hd : 1 ≤ d) (b0 : CoefIdx N n d → ℝ) (u : Fin N → ℝ) (a : Fin n) :
    bwEval (mixW b0 0) u a = b0 (a, mono0 N d) + ∑ j, b0 (a, mono1 N d hd j) * u j := by
  classical
  let f : Option (Fin N) → MonoIdx N d := fun o => o.elim (mono0 N d) (mono1 N d hd)
  have hf : Function.Injective f := by
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some j =>
        have := congrArg (fun m : MonoIdx N d => m.1.val) hxy
        simp [f, mono0, mono1] at this
    | some i =>
      cases y with
      | none =>
        have := congrArg (fun m : MonoIdx N d => m.1.val) hxy
        simp [f, mono0, mono1] at this
      | some j =>
        have := congrArg (fun m : MonoIdx N d => m.2.val) hxy
        simp only [f, Option.elim, mono1] at this
        have h2 : i = j := by simpa using this
        rw [h2]
  unfold bwEval
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))]
  · rw [Finset.sum_image (fun x _ y _ h => hf h), Fintype.sum_option]
    simp only [f, Option.elim, mixW, MonoIdx.deg]
    have h0 : ¬ (2 ≤ (mono0 N d).1.val) := by simp [mono0]
    have h1 : ∀ j, ¬ (2 ≤ (mono1 N d hd j).1.val) := by intro j; simp [mono1]
    simp only [h0, h1, ite_false, monoVal_mono1, monoVal_deg_zero u (mono0 N d) rfl, mul_one]
  · intro m _ hm
    by_cases h2 : 2 ≤ m.1.val
    · simp [mixW, MonoIdx.deg, h2]
    · exfalso
      apply hm
      rw [Finset.mem_image]
      by_cases h0 : m.1.val = 0
      · exact ⟨none, Finset.mem_univ _, (eq_mono0 m h0).symm⟩
      · obtain ⟨j, hj⟩ := eq_mono1 hd m (by omega)
        exact ⟨some j, Finset.mem_univ _, hj.symm⟩

/-- **The value of `g` is `gVal`**: the program reads the coefficients of degree `0` and `1` of
`b0` only. -/
theorem gProg_eval_gVal (hd : 1 ≤ r * dA) (b0 : CoefIdx (r * n) n (r * dA) → ℝ) (τ : ℝ)
    (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (ω : Fin k → (Fin (r * n) → ℝ) × (Fin n → ℝ)) :
    (gProg r n dA dF k).eval
        (gInVal (fun a => b0 (a, mono0 (r * n) (r * dA)))
          (fun a j => b0 (a, mono1 (r * n) (r * dA) hd j)) τ A F
          (fun i => (ω i).1) (fun i => (ω i).2)) () =
      gVal b0 τ (phiAF A F) ω := by
  rw [gProg_eval]
  unfold gVal standIn phiAF
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 3
  funext a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lowEval hd]

/-! ## A lower bound for every program that computes one sample -/

section lower

variable {ι : Type}

/-- The inputs that an argument mentions. -/
def argInps : Arg ι → List ι
  | .inp i => [i]
  | _ => []

/-- The inputs that a program mentions (in its instructions or in its output). -/
def progInps (p : SProg ι Unit) : List ι :=
  p.body.flatMap (fun I => argInps I.a ++ argInps I.b) ++ argInps (p.out ())

theorem argInps_length (a : Arg ι) : (argInps a).length ≤ 1 := by
  cases a <;> simp [argInps]

/-- A program mentions at most `2·cost + 1` inputs. -/
theorem progInps_length (p : SProg ι Unit) : (progInps p).length ≤ 2 * p.cost + 1 := by
  have h : ∀ l : List (SInstr ι),
      (l.flatMap (fun I => argInps I.a ++ argInps I.b)).length ≤ 2 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons I l ih =>
      have ha := argInps_length I.a
      have hb := argInps_length I.b
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have h1 := h p.body
  have h2 := argInps_length (p.out ())
  simp only [progInps, List.length_append, SProg.cost]
  omega

theorem arg_eval_congr (v v' : ι → ℝ) (R : List ℝ) (a : Arg ι)
    (h : ∀ i ∈ argInps a, v i = v' i) : a.eval v R = a.eval v' R := by
  cases a with
  | inp i => exact h i (by simp [argInps])
  | reg r => rfl
  | cst q => rfl

theorem srun_congr (v v' : ι → ℝ) (l : List (SInstr ι)) (R : List ℝ)
    (h : ∀ i ∈ l.flatMap (fun I => argInps I.a ++ argInps I.b), v i = v' i) :
    srun v l R = srun v' l R := by
  induction l generalizing R with
  | nil => rfl
  | cons I l ih =>
    simp only [List.flatMap_cons, List.mem_append] at h
    simp only [srun]
    have hI : I.eval v R = I.eval v' R := by
      simp only [SInstr.eval]
      rw [arg_eval_congr v v' R I.a (fun i hi => h i (Or.inl (Or.inl hi))),
        arg_eval_congr v v' R I.b (fun i hi => h i (Or.inl (Or.inr hi)))]
    rw [hI]
    exact ih _ (fun i hi => h i (Or.inr hi))

/-- The value of a program depends only on the inputs that it mentions. -/
theorem eval_congr_inps (p : SProg ι Unit) (v v' : ι → ℝ)
    (h : ∀ i ∈ progInps p, v i = v' i) : p.eval v () = p.eval v' () := by
  simp only [progInps, List.mem_append] at h
  simp only [SProg.eval]
  rw [srun_congr v v' p.body [] (fun i hi => h i (Or.inl hi))]
  exact arg_eval_congr v v' _ _ (fun i hi => h i (Or.inr hi))

end lower

theorem monoVal_ones {N d : ℕ} (m : MonoIdx N d) : monoVal (fun _ : Fin N => (1 : ℝ)) m = 1 := by
  simp [monoVal]

/-- The number of coefficients of a polynomial map `ℝ^N → ℝⁿ` of degree at most `d`. -/
theorem card_coefIdx (N n d : ℕ) : Fintype.card (CoefIdx N n d) = n * (N + d).choose d := by
  rw [Fintype.card_prod, Fintype.card_fin, card_monoIdx]

/-- **A lower bound for every program of the model that computes one sample of `s_B`**: such a
program mentions every coefficient of `W`, and a program of cost `c` mentions at most `2c + 1`
inputs. -/
theorem sample_lower (p : SProg (SampleIn r n dA dF) Unit)
    (hp : ∀ u W A F, p.eval (sampleVal u W A F) () =
      bwEval F (bwEval A (sphProj (bwEval W u))) 0)
    (hdA : 1 ≤ dA) (hdF : 1 ≤ dF) :
    Fintype.card (CoefIdx (r * n) n (r * dA)) ≤ 2 * p.cost + 1 := by
  classical
  have hmem : ∀ c : CoefIdx (r * n) n (r * dA), (Sum.inr (Sum.inl c) : SampleIn r n dA dF) ∈
      progInps p := by
    rintro ⟨a, m⟩
    by_contra hc
    let ones : Fin (r * n) → ℝ := fun _ => 1
    let Aid : CoefIdx n n dA → ℝ := fun i => if i.2 = mono1 n dA hdA i.1 then 1 else 0
    let Fa : CoefIdx n 1 dF → ℝ := fun i => if i.2 = mono1 n dF hdF a then 1 else 0
    let W1 : CoefIdx (r * n) n (r * dA) → ℝ := Pi.single (a, m) 1
    have hA : ∀ x : Fin n → ℝ, bwEval Aid x = x := by
      intro x
      funext b
      simp [bwEval, Aid, monoVal_mono1]
    have hF : ∀ z : Fin n → ℝ, bwEval Fa z 0 = z a := by
      intro z
      simp [bwEval, Fa, monoVal_mono1]
    have hW0 : bwEval (0 : CoefIdx (r * n) n (r * dA) → ℝ) ones = 0 := by
      funext b
      simp [bwEval]
    have hW1 : bwEval W1 ones = Pi.single a 1 := by
      funext b
      simp only [bwEval, W1, ones, monoVal_ones, mul_one, Pi.single_apply, Prod.mk.injEq]
      by_cases hb : b = a
      · simp [hb]
      · simp [hb]
    have h0 := hp ones 0 Aid Fa
    have h1 := hp ones W1 Aid Fa
    rw [hA, hF, hW0] at h0
    rw [hA, hF, hW1] at h1
    have e : p.eval (sampleVal ones 0 Aid Fa) () = p.eval (sampleVal ones W1 Aid Fa) () := by
      apply eval_congr_inps
      intro i hi
      rcases i with u | c | c | c
      · rfl
      · have hne : c ≠ (a, m) := fun h => hc (h ▸ hi)
        simp [sampleVal, W1, hne]
      · rfl
      · rfl
    rw [h0, h1] at e
    have hs : sphProj (Pi.single a (1 : ℝ)) a = 1 := by
      simp [sphProj, Pi.single_apply]
    rw [hs] at e
    simp [sphProj] at e
  let emb : CoefIdx (r * n) n (r * dA) ↪ SampleIn r n dA dF :=
    ⟨fun c => Sum.inr (Sum.inl c), fun x y h => by simpa using h⟩
  calc Fintype.card (CoefIdx (r * n) n (r * dA))
      = (Finset.univ.map emb).card := by simp
    _ ≤ (progInps p).toFinset.card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨c, -, rfl⟩ := Finset.mem_map.mp hi
        exact List.mem_toFinset.mpr (hmem c)
    _ ≤ (progInps p).length := List.toFinset_card_le _
    _ ≤ 2 * p.cost + 1 := progInps_length p

/-- The lower bound for the explicit scheme of one sample of `s_B`. -/
theorem sampleProg'_cost_lower (r n dA dF : ℕ) (hdA : 1 ≤ dA) (hdF : 1 ≤ dF) :
    n * (r * n + r * dA).choose (r * dA) ≤ 2 * (sampleProg' r n dA dF).cost + 1 := by
  rw [← card_coefIdx]
  exact sample_lower _ (fun u W A F => sampleProg'_eval u W A F) hdA hdF

/-! ## The comparisons at `r = 2`, `d_A, d_F ∈ {3, 4}`, `n ≥ 4096`, `k ≤ n²` -/

theorem choose3_le (n : ℕ) (hn : 4096 ≤ n) : (n + 3).choose 3 ≤ n ^ 3 := by
  have h1 : (n + 3).descFactorial 3 ≤ (n + 3) ^ 3 := Nat.descFactorial_le_pow _ _
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  have h2 : (10 * (n + 3)) ^ 3 ≤ (11 * n) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  rw [mul_pow, mul_pow] at h2
  have h3 : Nat.factorial 3 = 6 := rfl
  rw [h3] at h1
  norm_num at h2
  generalize (n + 3).choose 3 = X at *
  generalize (n + 3) ^ 3 = Y at *
  generalize n ^ 3 = Z at *
  omega

theorem choose4_le (n : ℕ) (hn : 4096 ≤ n) : (n + 4).choose 4 ≤ n ^ 4 := by
  have h1 : (n + 4).descFactorial 4 ≤ (n + 4) ^ 4 := Nat.descFactorial_le_pow _ _
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  have h2 : (10 * (n + 4)) ^ 4 ≤ (11 * n) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  rw [mul_pow, mul_pow] at h2
  have h3 : Nat.factorial 4 = 24 := rfl
  rw [h3] at h1
  norm_num at h2
  generalize (n + 4).choose 4 = X at *
  generalize (n + 4) ^ 4 = Y at *
  generalize n ^ 4 = Z at *
  omega

theorem chooseF_le (n dF : ℕ) (hn : 4096 ≤ n) (hdF : dF = 3 ∨ dF = 4) :
    (n + dF).choose dF ≤ n ^ 4 := by
  rcases hdF with rfl | rfl
  · exact (choose3_le n hn).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
  · exact choose4_le n hn

theorem choose6_ge (n : ℕ) : 64 * n ^ 6 ≤ 720 * (2 * n + 5).choose 6 := by
  have h1 := Nat.pow_sub_le_descFactorial (2 * n + 5) 6
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  have h3 : Nat.factorial 6 = 720 := rfl
  have h4 : 2 * n + 5 + 1 - 6 = 2 * n := by omega
  rw [h3, h4, mul_pow] at h1
  norm_num at h1
  exact h1

theorem choose8_ge (n : ℕ) : 256 * n ^ 8 ≤ 40320 * (2 * n + 7).choose 8 := by
  have h1 := Nat.pow_sub_le_descFactorial (2 * n + 7) 8
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  have h3 : Nat.factorial 8 = 40320 := rfl
  have h4 : 2 * n + 7 + 1 - 8 = 2 * n := by omega
  rw [h3, h4, mul_pow] at h1
  norm_num at h1
  exact h1

/-- `gCost ≤ k·(4n² + 5n + 1 + X + 2nX + 2Y) + k`, `X`, `Y` the numbers of monomials of `A` and
of `F`. -/
theorem gCost_le (k n dA dF : ℕ) :
    gCost k 2 n dA dF ≤ k * (4 * n ^ 2 + 5 * n + 1 + ((n + dA).choose dA +
      2 * n * (n + dA).choose dA) + 2 * (n + dF).choose dF) + k := by
  unfold gCost Ecost
  have h1 : (n + dA).choose dA - 1 - n ≤ (n + dA).choose dA :=
    (Nat.sub_le _ _).trans (Nat.sub_le _ _)
  have h2 : 2 * n * ((n + dA).choose dA - 1) ≤ 2 * n * (n + dA).choose dA :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h3 : 2 * (n + dF).choose dF - 2 ≤ 2 * (n + dF).choose dF := Nat.sub_le _ _
  refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _
  have h4 : 2 * 2 * n ^ 2 = 4 * n ^ 2 := by ring
  omega

/-- The comparison with the number of coefficients of `W` of top degree, in the form
`2·gCost + 1 < n · C(2n + 2d_A − 1, 2d_A)`. -/
theorem two_gCost_lt_top (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : k ≤ n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4) :
    2 * gCost k 2 n dA dF + 1 < n * (2 * n + 2 * dA - 1).choose (2 * dA) := by
  have hY := chooseF_le n dF hn hdF
  have hg := gCost_le k n dA dF
  have hn1 : 1 ≤ n := by omega
  have e2 : n ^ 2 = n * n := by ring
  have e3 : n ^ 3 = n * n ^ 2 := by ring
  have e4 : n ^ 4 = n * n ^ 3 := by ring
  have e5 : n ^ 5 = n * n ^ 4 := by ring
  have p2 : 4096 * n ≤ n ^ 2 := by rw [e2]; exact Nat.mul_le_mul_right _ hn
  have p3 : 4096 * n ^ 2 ≤ n ^ 3 := by rw [e3]; exact Nat.mul_le_mul_right _ hn
  have p4 : 4096 * n ^ 3 ≤ n ^ 4 := by rw [e4]; exact Nat.mul_le_mul_right _ hn
  have p5 : 4096 * n ^ 4 ≤ n ^ 5 := by rw [e5]; exact Nat.mul_le_mul_right _ hn
  rcases hdA with rfl | rfl
  · -- `d_A = 3`
    have hX := choose3_le n hn
    have hT := choose6_ge n
    have e : 2 * n + 2 * 3 - 1 = 2 * n + 5 := by omega
    rw [e]
    have hXn : 2 * n * (n + 3).choose 3 ≤ 2 * n ^ 4 := by
      have := Nat.mul_le_mul_left (2 * n) hX
      calc 2 * n * (n + 3).choose 3 ≤ 2 * n * n ^ 3 := this
        _ = 2 * n ^ 4 := by ring
    have hS : 4 * n ^ 2 + 5 * n + 1 + ((n + 3).choose 3 + 2 * n * (n + 3).choose 3) +
        2 * (n + dF).choose dF ≤ 5 * n ^ 4 := by
      generalize (n + 3).choose 3 = X at *
      generalize (n + dF).choose dF = Y at *
      generalize 2 * n * X = Z at *
      omega
    have hkS := Nat.mul_le_mul hk hS
    have e6 : n ^ 2 * (5 * n ^ 4) = 5 * n ^ 6 := by ring
    rw [e6] at hkS
    have p6 : n ^ 2 ≤ n ^ 6 := Nat.pow_le_pow_right hn1 (by norm_num)
    have hG : 2 * gCost k 2 n 3 dF + 1 ≤ 13 * n ^ 6 := by
      have h61 : 1 ≤ n ^ 6 := Nat.one_le_pow _ _ hn1
      omega
    have e7 : n * n ^ 6 = n ^ 7 := by ring
    have p7 : 4096 * n ^ 6 ≤ n ^ 7 := by rw [← e7]; exact Nat.mul_le_mul_right _ hn
    have hnT : 64 * n ^ 7 ≤ 720 * (n * (2 * n + 5).choose 6) := by
      have := Nat.mul_le_mul_left n hT
      calc 64 * n ^ 7 = n * (64 * n ^ 6) := by ring
        _ ≤ n * (720 * (2 * n + 5).choose 6) := this
        _ = 720 * (n * (2 * n + 5).choose 6) := by ring
    have h61 : 1 ≤ n ^ 6 := Nat.one_le_pow _ _ hn1
    generalize n * (2 * n + 5).choose 6 = V at *
    omega
  · -- `d_A = 4`
    have hX := choose4_le n hn
    have hT := choose8_ge n
    have e : 2 * n + 2 * 4 - 1 = 2 * n + 7 := by omega
    have e' : 2 * 4 = 8 := rfl
    rw [e, e']
    have hXn : 2 * n * (n + 4).choose 4 ≤ 2 * n ^ 5 := by
      have := Nat.mul_le_mul_left (2 * n) hX
      calc 2 * n * (n + 4).choose 4 ≤ 2 * n * n ^ 4 := this
        _ = 2 * n ^ 5 := by ring
    have hS : 4 * n ^ 2 + 5 * n + 1 + ((n + 4).choose 4 + 2 * n * (n + 4).choose 4) +
        2 * (n + dF).choose dF ≤ 3 * n ^ 5 := by
      generalize (n + 4).choose 4 = X at *
      generalize (n + dF).choose dF = Y at *
      generalize 2 * n * X = Z at *
      omega
    have hkS := Nat.mul_le_mul hk hS
    have e6 : n ^ 2 * (3 * n ^ 5) = 3 * n ^ 7 := by ring
    rw [e6] at hkS
    have p6 : n ^ 2 ≤ n ^ 7 := Nat.pow_le_pow_right hn1 (by norm_num)
    have h71 : 1 ≤ n ^ 7 := Nat.one_le_pow _ _ hn1
    have hG : 2 * gCost k 2 n 4 dF + 1 ≤ 9 * n ^ 7 := by omega
    have e8 : n * n ^ 7 = n ^ 8 := by ring
    have e9 : n * n ^ 8 = n ^ 9 := by ring
    have p8 : 4096 * n ^ 7 ≤ n ^ 8 := by rw [← e8]; exact Nat.mul_le_mul_right _ hn
    have p9 : 4096 * n ^ 8 ≤ n ^ 9 := by rw [← e9]; exact Nat.mul_le_mul_right _ hn
    have hnT : 256 * n ^ 9 ≤ 40320 * (n * (2 * n + 7).choose 8) := by
      have := Nat.mul_le_mul_left n hT
      calc 256 * n ^ 9 = n * (256 * n ^ 8) := by ring
        _ ≤ n * (40320 * (2 * n + 7).choose 8) := this
        _ = 40320 * (n * (2 * n + 7).choose 8) := by ring
    generalize n * (2 * n + 7).choose 8 = V at *
    omega

/-- **`gCost` is below the number of coefficients of `W` of top degree** (`n` outputs times
`C(2n + 2d_A − 1, 2d_A)` monomials of degree exactly `2d_A` in `2n` variables). -/
theorem gCost_lt_top (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : k ≤ n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4) :
    gCost k 2 n dA dF < n * (2 * n + 2 * dA - 1).choose (2 * dA) := by
  have := two_gCost_lt_top n k dA dF hn hk hdA hdF
  omega

/-- **`gCost` is below the lower bound of `sample_lower`**: `2·gCost + 1 < D_W`,
`D_W = n · C(2n + 2d_A, 2d_A)` the number of coefficients of `W`. -/
theorem gCost_lt_lower (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : k ≤ n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4) :
    2 * gCost k 2 n dA dF + 1 < n * (2 * n + 2 * dA).choose (2 * dA) := by
  refine (two_gCost_lt_top n k dA dF hn hk hdA hdF).trans_le (Nat.mul_le_mul_left _ ?_)
  exact Nat.choose_le_choose _ (by omega)

/-- **The cost of `g` is below the cost of every program of the model that computes one sample
of `s_B`** (for all inputs `u`, `W`, `A`, `F`). -/
theorem gProg_cost_lt_any (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : k ≤ n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4) (p : SProg (SampleIn 2 n dA dF) Unit)
    (hp : ∀ u W A F, p.eval (sampleVal u W A F) () =
      bwEval F (bwEval A (sphProj (bwEval W u))) 0) :
    (gProg 2 n dA dF k).cost < p.cost := by
  have h1 := gProg_cost 2 n dA dF k
  have h2 := gCost_lt_lower n k dA dF hn hk hdA hdF
  have h3 := sample_lower p hp (by omega) (by omega)
  rw [card_coefIdx] at h3
  omega

/-- The cost of `g` is below the cost of the explicit scheme `sampleProg'` of one sample. -/
theorem gProg_cost_lt_sampleProg' (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : k ≤ n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4) :
    (gProg 2 n dA dF k).cost < (sampleProg' 2 n dA dF).cost :=
  gProg_cost_lt_any n k dA dF hn hk hdA hdF _ (fun u W A F => sampleProg'_eval u W A F)

/-- `gCost` is below the cost bound `sampleCost'` of one sample of `s_B`. -/
theorem gCost_lt_sampleCost' (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : k ≤ n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4) :
    gCost k 2 n dA dF < sampleCost' 2 n dA dF := by
  have h2 := gCost_lt_lower n k dA dF hn hk hdA hdF
  have h3 := sampleProg'_cost_lower 2 n dA dF (by omega) (by omega)
  have h4 := sampleProg'_cost 2 n dA dF
  omega

/-- The number of coefficients of top degree `d` of a polynomial map `ℝ^N → ℝⁿ`. -/
theorem topCoef_card (N n d : ℕ) :
    (Finset.univ.filter fun i : CoefIdx N n d => i.2.deg = d).card =
      n * (N + d - 1).choose d := by
  classical
  have h1 : (Finset.univ.filter fun i : CoefIdx N n d => i.2.deg = d) =
      (Finset.univ : Finset (Fin n)) ×ˢ
        (({Fin.last d} : Finset (Fin (d + 1))).sigma fun j =>
          (Finset.univ : Finset (Sym (Fin N) j))) := by
    ext ⟨a, j, s⟩
    simp only [Finset.mem_univ, true_and, MonoIdx.deg, Finset.mem_product,
      Finset.mem_sigma, Finset.mem_singleton, and_true, Fin.ext_iff, Fin.val_last]
    refine Finset.mem_filter.trans ?_
    simp
  rw [h1, Finset.card_product, Finset.card_sigma, Finset.sum_singleton, Finset.card_univ,
    Finset.card_univ, Sym.card_sym_eq_multichoose, Nat.multichoose_eq, Fintype.card_fin,
    Fintype.card_fin, Fin.val_last]

/-! ## The program with a fixed rational noise level -/

/-- The input renaming of `gProgFix`: the slot of `τ` reads the computed square root. -/
def fixIn (r n dA dF k : ℕ) : GIn r n dA dF k → GIn r n dA dF k ⊕ Unit
  | .inr (.inl _) => .inr ()
  | x => .inl x

/-- **The program with the fixed noise level `τ = √q`**, `q` a rational constant: one square
root, then `gProg`. The input slot of `τ` is not read. -/
def gProgFix (q : ℚ) (r n dA dF k : ℕ) : SProg (GIn r n dA dF k) Unit :=
  (SProg.sqrt1 (.cst q)).bind ((gProg r n dA dF k).mapIn (fixIn r n dA dF k))

theorem gProgFix_eval (q : ℚ) (w0 : Fin n → ℝ) (w1 : Fin n → Fin (r * n) → ℝ) (τ : ℝ)
    (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) (us : Fin k → Fin (r * n) → ℝ)
    (gs : Fin k → Fin n → ℝ) :
    (gProgFix q r n dA dF k).eval (gInVal w0 w1 τ A F us gs) () =
      (gProg r n dA dF k).eval (gInVal w0 w1 (Real.sqrt (q : ℝ)) A F us gs) () := by
  rw [gProgFix, SProg.eval_bind, SProg.eval_mapIn]
  congr 1
  funext x
  rcases x with x | x | x
  · rfl
  · simp [fixIn, gInVal, Arg.eval]
  · rfl

theorem gProgFix_cost (q : ℚ) (r n dA dF k : ℕ) :
    (gProgFix q r n dA dF k).cost ≤ gCost k r n dA dF + 1 := by
  have := gProg_cost r n dA dF k
  simp only [gProgFix, SProg.cost_bind, SProg.cost_sqrt1, SProg.cost_mapIn]
  omega

end

end BstLean.Part106

#print axioms BstLean.Part106.gProg_eval
#print axioms BstLean.Part106.gProg_cost
#print axioms BstLean.Part106.lowEval
#print axioms BstLean.Part106.gProg_eval_gVal
#print axioms BstLean.Part106.sample_lower
#print axioms BstLean.Part106.card_coefIdx
#print axioms BstLean.Part106.sampleProg'_cost_lower
#print axioms BstLean.Part106.gCost_lt_lower
#print axioms BstLean.Part106.gCost_lt_top
#print axioms BstLean.Part106.gProg_cost_lt_any
#print axioms BstLean.Part106.gProg_cost_lt_sampleProg'
#print axioms BstLean.Part106.gCost_lt_sampleCost'
#print axioms BstLean.Part106.topCoef_card
#print axioms BstLean.Part106.gProgFix_eval
#print axioms BstLean.Part106.gProgFix_cost
