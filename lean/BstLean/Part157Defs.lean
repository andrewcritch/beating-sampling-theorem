import BstLean.Part134All
import BstLean.Part136Kern
import BstLean.Part156All

/-!
# Part 157, item 1: the classifier objects for the actual networks

Role: `delegations/statements/p157-spec.md`, item 1. Compare with `MM.md` (the classifier
question) and `proofs/option-n/theorem7-01-statement-program.tex`, "Setting and assertion".
Do not use `sorry`, `native_decide` or `axiom`.

* `classifier F t z`: the proposition `F(z) > t` (the classifier `c` is true at `z`).
* `hitSet W A F t`: the set of the inputs `u` with `c(A(x)) = true`, `x = W(u)/|W(u)|` (`sphPt`,
  with the fixed point `e0` when `W(u) = 0`).
* `pTarget W A F t = Pr_u(c(A(x)))`, `u` uniform on the unit sphere of `ℝ^N`.
* `pTargetT θ t`: the same for the triple `θ = (W, A, F)`.
* `measurable_pTargetT`: `pTargetT` is measurable in the weights; `pTarget_nonneg`,
  `pTarget_le_one`.
* `successNet θ t U`: the success criterion `p ≤ U ≤ max (10 p) (1/100)` of Part 156 for the
  actual target; `outRule` of Part 156 is the output rule.
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130
open BstLean.Part156 (success outRule)

variable {N n mW' mA' mF' : ℕ}

/-- **The classifier** `c(z) = true` exactly when `F(z) > t`. -/
def classifier (F : MlpParam n mF' 1) (t : ℝ) (z : Fin n → ℝ) : Prop := t < mlpEval F z 0

/-- The inputs `u` at which the classifier is true on `A(x)`, `x = W(u)/|W(u)|`. -/
def hitSet (W : MlpParam N mW' n) (A : MlpParam n mA' n) (F : MlpParam n mF' 1) (t : ℝ) :
    Set (Fin N → ℝ) :=
  {u | classifier F t (mlpEval A (sphPt (mlpEval W u)))}

/-- **The target** `p(W, A, F) = Pr_u(c(A(x)) = true)`, `u` uniform on the unit sphere of `ℝ^N`
and `x = W(u)/|W(u)|` (the fixed point `e0 n` when `W(u) = 0`). -/
noncomputable def pTarget (W : MlpParam N mW' n) (A : MlpParam n mA' n) (F : MlpParam n mF' 1)
    (t : ℝ) : ℝ :=
  (uniformSphere N).real (hitSet W A F t)

/-- The triple of the weights of `W`, `A`, `F`. -/
abbrev Triple (N mW' n mA' mF' : ℕ) : Type :=
  MlpParam N mW' n × MlpParam n mA' n × MlpParam n mF' 1

/-- The target as a function of the triple `(W, A, F)`. -/
noncomputable def pTargetT (θ : Triple N mW' n mA' mF') (t : ℝ) : ℝ :=
  pTarget θ.1 θ.2.1 θ.2.2 t

/-- `(θ, u) ↦ F(A(x_W(u)))` is measurable. -/
lemma measurable_score :
    Measurable (fun q : Triple N mW' n mA' mF' × (Fin N → ℝ) =>
      mlpEval q.1.2.2 (mlpEval q.1.2.1 (sphPt (mlpEval q.1.1 q.2))) 0) := by
  have h1 : Measurable (fun q : Triple N mW' n mA' mF' × (Fin N → ℝ) =>
      sphPt (mlpEval q.1.1 q.2)) :=
    measurable_sphPt.comp (continuous_mlpEval_joint.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have h2 : Measurable (fun q : Triple N mW' n mA' mF' × (Fin N → ℝ) =>
      mlpEval q.1.2.1 (sphPt (mlpEval q.1.1 q.2))) :=
    continuous_mlpEval_joint.measurable.comp
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk h1)
  have h3 : Measurable (fun q : Triple N mW' n mA' mF' × (Fin N → ℝ) =>
      mlpEval q.1.2.2 (mlpEval q.1.2.1 (sphPt (mlpEval q.1.1 q.2)))) :=
    continuous_mlpEval_joint.measurable.comp
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk h2)
  exact (measurable_pi_apply 0).comp h3

/-- The set of the pairs `(θ, u)` at which the classifier is true is measurable. -/
lemma measurableSet_hit (t : ℝ) :
    MeasurableSet {q : Triple N mW' n mA' mF' × (Fin N → ℝ) |
      classifier q.1.2.2 t (mlpEval q.1.2.1 (sphPt (mlpEval q.1.1 q.2)))} :=
  measurableSet_lt measurable_const measurable_score

lemma measurableSet_hitSet (W : MlpParam N mW' n) (A : MlpParam n mA' n) (F : MlpParam n mF' 1)
    (t : ℝ) : MeasurableSet (hitSet W A F t) :=
  (measurableSet_hit (N := N) t).preimage (measurable_prodMk_left (x := (W, A, F)))

/-- **The target is measurable in the weights** (jointly in `(W, A, F)`). -/
theorem measurable_pTargetT (t : ℝ) :
    Measurable (fun θ : Triple N mW' n mA' mF' => pTargetT θ t) := by
  exact (measurable_measure_prodMk_left (ν := uniformSphere N)
    (measurableSet_hit (N := N) (mW' := mW') (mA' := mA') (mF' := mF') t)).ennreal_toReal

lemma pTarget_nonneg (W : MlpParam N mW' n) (A : MlpParam n mA' n) (F : MlpParam n mF' 1)
    (t : ℝ) : 0 ≤ pTarget W A F t := measureReal_nonneg

lemma pTarget_le_one (hN : 1 ≤ N) (W : MlpParam N mW' n) (A : MlpParam n mA' n)
    (F : MlpParam n mF' 1) (t : ℝ) : pTarget W A F t ≤ 1 := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  exact measureReal_le_one

/-- The target is the measure of `{x | F(A(x)) > t}` under `μ_W` (`muWn` of Part 130). -/
theorem pTarget_eq_muWn (W : MlpParam N mW' n) (A : MlpParam n mA' n) (F : MlpParam n mF' 1)
    (t : ℝ) : pTarget W A F t = (muWn W).real {x | t < phiN A F x} := by
  have hs : MeasurableSet {x : Fin n → ℝ | t < phiN A F x} :=
    measurableSet_lt measurable_const (continuous_phiN A F).measurable
  unfold pTarget muWn
  rw [map_measureReal_apply (measurable_sphPt_mlpEval W) hs]
  rfl

/-- **The success criterion for the actual networks**: `p ≤ U ≤ max (10 p) (1/100)` with
`p = pTarget W A F t` (`success` of Part 156). -/
def successNet (θ : Triple N mW' n mA' mF') (t U : ℝ) : Prop := success (pTargetT θ t) U

lemma successNet_iff (θ : Triple N mW' n mA' mF') (t U : ℝ) :
    successNet θ t U ↔ pTargetT θ t ≤ U ∧ U ≤ max (10 * pTargetT θ t) (1 / 100) := Iff.rfl

/-- The output rule never fails by an output above `1`, and `U ≥ 1/100`:
`1/100 ≤ outRule a R ≤ 1`. -/
lemma outRule_mem (a R : ℝ) : 1 / 100 ≤ outRule a R ∧ outRule a R ≤ 1 := by
  unfold outRule
  refine ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

/-- The set of the pairs `(p, U)` with success is measurable. -/
lemma measurableSet_success {α : Type*} [MeasurableSpace α] {p U : α → ℝ} (hp : Measurable p)
    (hU : Measurable U) : MeasurableSet {x | success (p x) (U x)} := by
  unfold success
  exact (measurableSet_le hp hU).inter
    (measurableSet_le hU ((measurable_const.mul hp).max measurable_const))

lemma measurable_outRule {α : Type*} [MeasurableSpace α] (a : ℝ) {R : α → ℝ}
    (hR : Measurable R) : Measurable (fun x => outRule a (R x)) := by
  unfold outRule
  exact measurable_const.min (measurable_const.max (measurable_const.mul hR))

end BstLean.Part157

open BstLean.Part157 in
#print axioms measurable_pTargetT
open BstLean.Part157 in
#print axioms pTarget_eq_muWn
