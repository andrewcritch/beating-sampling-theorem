import BstLean.Part157Triple

/-!
# Part 157, items 3 and 4: the design, the sampling program, the stand-in probability

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-01-statement-program.tex`, the ordered program, steps 6 and 7;
`theorem7-03-composition.tex`, "Two-stage composition" and Lemma `t7:p03:sampling`.

* `Design n`: the two centres (`Centres n`), the scalar `τ₀` and the stored mixture table
  `mix c s = (λ̃, S̃)` (location factor and scale at the latitude `s`), all measurable functions of
  the retained data. The steps 1 to 5 of the paper's program compute one such design; the steps
  are NOT defined in Lean (see the report).
* `DrawSp n`, `drawMeas n`: one draw of the program: `Z`, `G₁, …, G_{n−1}`, `η`, independent
  standard Gaussian.
* `latitude`, `drawY`, `hitFn`: step 6: `a_x = |ĉ| + τ₀ Z`, `r_x² = τ₀² Σ G_i²`,
  `s = a_x/√(a_x² + r_x²)`, `y = λ̃ c_A + √S̃ η`, hit exactly when `F(y) > t`.
* `hits D t k i`: the `i`-th of `k` draws; `sampMeas k n`: the distribution of the `k` draws;
  `qTilde D t c`: the probability of a hit given the retained data `c`.
* `hits_indep`, `hits_mean`, `hits_01`: for every retained value, the draws are independent, with
  values in `{0, 1}` and mean `qTilde` (item 4).
* `pRes D t c ω`: the target of the triple `rebuild D c ω`.
* `PStand D t c ω_A`: the stand-in probability `∫ c(A(x)) dν'(x)`, `ν'` the distribution of
  `sphPt (ĉ + τ₀ ξ)`, `A` the Agent network with residual matrix `ω_A`.
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)

/-- **A design**: the two centres, the scalar `τ₀` of the stand-in input, and the mixture table
`mix c s = (λ̃, S̃)` of the sampling step, all measurable in the retained data. -/
structure Design (n : ℕ) extends Centres n where
  /-- The scalar `τ₀` of the stand-in input `sphPt (ĉ + τ₀ ξ)`. -/
  tau0 : Ret n → ℝ
  /-- The stored table: at the latitude `s`, the location factor `λ̃` and the scale `S̃`. -/
  mix : Ret n → ℝ → ℝ × ℝ
  mtau0 : Measurable tau0
  mmix : Measurable (fun p : Ret n × ℝ => mix p.1 p.2)

variable {n : ℕ}

/-! ## The sampling program (steps 6 and 7 of the paper's program) -/

/-- One draw of the program: `((Z, (G₁, …, G_{n−1})), η)`. -/
abbrev DrawSp (n : ℕ) : Type := (ℝ × (Fin (n - 1) → ℝ)) × (Fin n → ℝ)

/-- The distribution of one draw: independent standard Gaussian numbers. -/
noncomputable def drawMeas (n : ℕ) : Measure (DrawSp n) :=
  ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1)))).prod (stdGauss (Fin n))

instance : IsProbabilityMeasure (drawMeas n) := by unfold drawMeas; infer_instance

/-- The latitude of a draw: `s = a_x/√(a_x² + r_x²)`, `a_x = a + τ Z`, `r_x² = τ² Σ G_i²`
(division by zero gives `0`). -/
noncomputable def latitude (a τ : ℝ) (z : ℝ × (Fin (n - 1) → ℝ)) : ℝ :=
  (a + τ * z.1) / √((a + τ * z.1) ^ 2 + τ ^ 2 * normSq z.2)

/-- The input of `F` in a draw: `y = λ̃ c_A + √S̃ η`, with `(λ̃, S̃)` the table at the latitude. -/
noncomputable def drawY (D : Design n) (c : Ret n) (d : DrawSp n) : Fin n → ℝ :=
  (D.mix c (latitude (√(normSq c.1.2)) (D.tau0 c) d.1)).1 • c.2.1.2 +
    √((D.mix c (latitude (√(normSq c.1.2)) (D.tau0 c) d.1)).2) • d.2

/-- The event of a hit: `F(y) > t`. -/
def hitEv (D : Design n) (t : ℝ) : Set (Ret n × DrawSp n) :=
  {x | classifier x.1.2.2 t (drawY D x.1 x.2)}

/-- The value of a draw: `1` for a hit, `0` otherwise. -/
noncomputable def hitFn (D : Design n) (t : ℝ) (x : Ret n × DrawSp n) : ℝ :=
  (hitEv D t).indicator 1 x

/-- The `i`-th of the `k` draws of the program, as a function of the retained data and of all
the draws. -/
noncomputable def hits (D : Design n) (t : ℝ) (k : ℕ) (i : Fin k)
    (x : Ret n × (Fin k → DrawSp n)) : ℝ :=
  hitFn D t (x.1, x.2 i)

/-- The distribution of the `k` draws: independent, each with the distribution `drawMeas n`. -/
noncomputable def sampMeas (k n : ℕ) : Measure (Fin k → DrawSp n) :=
  Measure.pi fun _ => drawMeas n

instance (k : ℕ) : IsProbabilityMeasure (sampMeas k n) := by unfold sampMeas; infer_instance

/-- **The stand-in mean** `q̃`: the probability of a hit in one draw, given the retained data. -/
noncomputable def qTilde (D : Design n) (t : ℝ) (c : Ret n) : ℝ :=
  ∫ d, hitFn D t (c, d) ∂drawMeas n

lemma measurable_latitude_comp {α : Type*} [MeasurableSpace α] {a τ : α → ℝ}
    {z : α → ℝ × (Fin (n - 1) → ℝ)} (ha : Measurable a) (hτ : Measurable τ) (hz : Measurable z) :
    Measurable (fun x => latitude (a x) (τ x) (z x)) := by
  unfold latitude
  have h1 : Measurable (fun x => a x + τ x * (z x).1) := ha.add (hτ.mul (measurable_fst.comp hz))
  have h2 : Measurable (fun x => normSq (z x).2) :=
    continuous_normSq.measurable.comp (measurable_snd.comp hz)
  exact h1.div (((h1.pow_const 2).add ((hτ.pow_const 2).mul h2)).sqrt)

lemma measurable_drawY (D : Design n) :
    Measurable (fun x : Ret n × DrawSp n => drawY D x.1 x.2) := by
  unfold drawY
  have hs : Measurable (fun x : Ret n × DrawSp n =>
      latitude (√(normSq x.1.1.2)) (D.tau0 x.1) x.2.1) :=
    measurable_latitude_comp
      ((continuous_normSq.measurable.comp
        (measurable_snd.comp (measurable_fst.comp measurable_fst))).sqrt)
      (D.mtau0.comp measurable_fst) (measurable_fst.comp measurable_snd)
  have hm : Measurable (fun x : Ret n × DrawSp n =>
      D.mix x.1 (latitude (√(normSq x.1.1.2)) (D.tau0 x.1) x.2.1)) :=
    D.mmix.comp (measurable_fst.prodMk hs)
  have hcA : Measurable (fun x : Ret n × DrawSp n => x.1.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
  exact ((measurable_fst.comp hm).smul hcA).add
    (((measurable_snd.comp hm).sqrt).smul (measurable_snd.comp measurable_snd))

lemma measurableSet_hitEv (D : Design n) (t : ℝ) : MeasurableSet (hitEv D t) := by
  have h : Measurable (fun x : Ret n × DrawSp n => mlpEval x.1.2.2 (drawY D x.1 x.2)) :=
    continuous_mlpEval_joint.measurable.comp
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk (measurable_drawY D))
  exact measurableSet_lt measurable_const ((measurable_pi_apply 0).comp h)

lemma measurable_hitFn (D : Design n) (t : ℝ) : Measurable (hitFn D t) :=
  measurable_one.indicator (measurableSet_hitEv D t)

lemma measurable_hits (D : Design n) (t : ℝ) (k : ℕ) (i : Fin k) : Measurable (hits D t k i) :=
  (measurable_hitFn D t).comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

/-- A draw has the value `0` or `1`. -/
lemma hitFn_01 (D : Design n) (t : ℝ) (x : Ret n × DrawSp n) :
    hitFn D t x = 0 ∨ hitFn D t x = 1 := by
  unfold hitFn
  by_cases h : x ∈ hitEv D t
  · right; simp [h]
  · left; simp [h]

lemma hits_01 (D : Design n) (t : ℝ) (k : ℕ) (i : Fin k) (x : Ret n × (Fin k → DrawSp n)) :
    hits D t k i x = 0 ∨ hits D t k i x = 1 := hitFn_01 D t _

/-- **The draws are independent** (for every retained value `c`). -/
theorem hits_indep (D : Design n) (t : ℝ) (k : ℕ) (c : Ret n) :
    iIndepFun (fun i σ => hits D t k i (c, σ)) (sampMeas k n) := by
  unfold sampMeas
  exact iIndepFun_pi (X := fun (_ : Fin k) (d : DrawSp n) => hitFn D t (c, d))
    (fun _ => ((measurable_hitFn D t).comp measurable_prodMk_left).aemeasurable)

/-- **Each draw has the stand-in mean** `q̃` (for every retained value `c`): the draws are
Bernoulli variables with mean `qTilde D t c`. -/
theorem hits_mean (D : Design n) (t : ℝ) (k : ℕ) (c : Ret n) (i : Fin k) :
    ∫ σ, hits D t k i (c, σ) ∂sampMeas k n = qTilde D t c := by
  unfold sampMeas qTilde
  exact integral_comp_eval (μ := fun _ : Fin k => drawMeas n) (i := i)
    (f := fun d : DrawSp n => hitFn D t (c, d))
    ((measurable_hitFn D t).comp measurable_prodMk_left).aestronglyMeasurable

/-- `q̃` is the probability of the event of a hit. -/
theorem qTilde_eq (D : Design n) (t : ℝ) (c : Ret n) :
    qTilde D t c = (drawMeas n).real {d | classifier c.2.2 t (drawY D c d)} := by
  unfold qTilde hitFn
  have hs : MeasurableSet {d : DrawSp n | classifier c.2.2 t (drawY D c d)} :=
    (measurableSet_hitEv D t).preimage measurable_prodMk_left
  have e : (fun d : DrawSp n => (hitEv D t).indicator (1 : Ret n × DrawSp n → ℝ) (c, d)) =
      {d : DrawSp n | classifier c.2.2 t (drawY D c d)}.indicator 1 := by
    funext d
    by_cases h : (c, d) ∈ hitEv D t
    · have h' : d ∈ {d : DrawSp n | classifier c.2.2 t (drawY D c d)} := h
      simp [h, h']
    · have h' : d ∉ {d : DrawSp n | classifier c.2.2 t (drawY D c d)} := h
      simp [h, h']
  rw [e, integral_indicator_one hs]

/-! ## The target and the stand-in probability as functions of the residual matrices -/

/-- **The target as a function of the retained data and the residual matrices.** -/
noncomputable def pRes (D : Centres n) (t : ℝ) (c : Ret n) (ω : ResW n × ResA n) : ℝ :=
  pTargetT (rebuild D c ω) t

/-- The Agent network with retained data `c` and residual matrix `ω_A`. -/
noncomputable def agentOf (D : Centres n) (c : Ret n) (ωA : ResA n) : MlpParam n (mA n) n :=
  netOf (D.bA c.1) c.2.1.1 c.2.1.2 ωA

lemma rebuild_agent (D : Centres n) (c : Ret n) (ω : ResW n × ResA n) :
    (rebuild D c ω).2.1 = agentOf D c ω.2 := rfl

/-- **The stand-in probability** `P = ∫ c(A(x)) dν'(x)`: `ν'` is the distribution of
`sphPt (ĉ + τ₀ ξ)`, `ξ` a standard Gaussian vector of `ℝⁿ`, and `A` is the Agent network with
retained data `c` and residual matrix `ω_A`. -/
noncomputable def PStand (D : Design n) (t : ℝ) (c : Ret n) (ωA : ResA n) : ℝ :=
  (stdGauss (Fin n)).real
    {ξ | classifier c.2.2 t (mlpEval (agentOf D.toCentres c ωA) (sphPt (c.1.2 + D.tau0 c • ξ)))}

lemma measurable_pRes (D : Centres n) (t : ℝ) :
    Measurable (fun p : Ret n × (ResW n × ResA n) => pRes D t p.1 p.2) :=
  (measurable_pTargetT t).comp (measurable_rebuild D)

lemma measurable_PStand (D : Design n) (t : ℝ) (c : Ret n) : Measurable (PStand D t c) := by
  have hA : Measurable (fun y : ResA n × (Fin n → ℝ) => agentOf D.toCentres c y.1) :=
    measurable_netOf_comp (b := fun _ : ResA n × (Fin n → ℝ) => D.bA c.1)
      ((D.mbA.comp measurable_prodMk_left).comp measurable_snd) measurable_const measurable_const
      measurable_fst
  have hx : Measurable (fun y : ResA n × (Fin n → ℝ) => sphPt (c.1.2 + D.tau0 c • y.2)) :=
    measurable_sphPt.comp (measurable_const.add
      ((measurable_const_smul (D.tau0 c)).comp measurable_snd))
  have h1 : Measurable (fun y : ResA n × (Fin n → ℝ) =>
      mlpEval (agentOf D.toCentres c y.1) (sphPt (c.1.2 + D.tau0 c • y.2))) :=
    continuous_mlpEval_joint.measurable.comp (hA.prodMk hx)
  have h2 : Measurable (fun y : ResA n × (Fin n → ℝ) =>
      mlpEval c.2.2 (mlpEval (agentOf D.toCentres c y.1) (sphPt (c.1.2 + D.tau0 c • y.2))) 0) :=
    (measurable_pi_apply 0).comp
      (continuous_mlpEval_joint.measurable.comp (measurable_const.prodMk h1))
  have hS : MeasurableSet {y : ResA n × (Fin n → ℝ) |
      classifier c.2.2 t (mlpEval (agentOf D.toCentres c y.1) (sphPt (c.1.2 + D.tau0 c • y.2)))} :=
    measurableSet_lt measurable_const h2
  exact (measurable_measure_prodMk_left (ν := stdGauss (Fin n)) hS).ennreal_toReal

lemma pRes_nonneg (D : Centres n) (t : ℝ) (c : Ret n) (ω : ResW n × ResA n) : 0 ≤ pRes D t c ω :=
  pTarget_nonneg _ _ _ _

lemma pRes_le_one (hn : 1 ≤ n) (D : Centres n) (t : ℝ) (c : Ret n) (ω : ResW n × ResA n) :
    pRes D t c ω ≤ 1 := pTarget_le_one (by omega) _ _ _ _

lemma PStand_nonneg (D : Design n) (t : ℝ) (c : Ret n) (ωA : ResA n) : 0 ≤ PStand D t c ωA :=
  measureReal_nonneg

lemma PStand_le_one (D : Design n) (t : ℝ) (c : Ret n) (ωA : ResA n) : PStand D t c ωA ≤ 1 :=
  measureReal_le_one

end BstLean.Part157

open BstLean.Part157 in
#print axioms hits_indep
open BstLean.Part157 in
#print axioms hits_mean
open BstLean.Part157 in
#print axioms qTilde_eq
open BstLean.Part157 in
#print axioms measurable_PStand
