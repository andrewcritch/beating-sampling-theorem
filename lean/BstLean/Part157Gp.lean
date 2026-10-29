import BstLean.Part157Final

/-!
# Part 157, items 3 and 5: (GP-W) and (GP-A) from one Gaussian inequality and two frame bounds

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-02-world.tex`, Lemma `t7:p02:GP` and Corollary `t7:p02:MGF`;
`theorem7-03-composition.tex`, Lemma `t7:p03:gp`.

* `GaussFrameMGF`: a NAMED HYPOTHESIS without networks: the bound of the moment generating
  function of `p(M) = μ{x | (x, M r(x)) ∈ S}` for a Gaussian matrix `M`, residual vectors
  `r(x) = res b (h x)` whose unit directions have the frame bound `L`. It is the statement of
  Corollary `t7:p02:MGF`. It is NOT proved in Lean.
* `FRAME_W_hyp`, `FRAME_A_hyp`: the two frame bounds of the actual networks. Each is a statement
  about the retained data only (no residual matrix occurs).
* `pRes_eq_frame`, `PStand_eq_frame`: the target and the stand-in probability in the form
  `μ{x | (x, M r(x)) ∈ S}` (from `mlp2_reb`).
* `gpw_of_frame`, `gpa_of_frame`: `GaussFrameMGF` and the frame bounds give `GPW_hyp`, `GPA_hyp`.
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part156

/-- **The Gaussian frame inequality in the indicator form (a named hypothesis; no network).**
`μ` is a probability measure on the inputs `x ∈ ℝ^N`; `h(x) ∈ ℝ^m` is a measurable field,
`r(x) = res b (h x)` its part orthogonal to `b` (for `b = 0`: `r = h`), and
`e(x) = r(x)/|r(x)|` (`0` where `r(x) = 0`). `M` is a Gaussian matrix with `q` rows, `m` columns
and entry variance `v > 0`. `S` is a measurable set of pairs (input, vector of `ℝ^q`). IF the
frame bound `∫ ⟨e(x), w⟩² dμ ≤ L·|w|²` holds for every `w`, with `L > 0`, THEN for
`p(M) = μ{x | (x, M r(x)) ∈ S}` and `q₀ = E_M p(M)`:
`E_M exp(s·p(M)/L) ≤ (1 − q₀ + q₀ e^s)^{1/L}` for every real `s`.

Paper statement that proves it: `theorem7-02-world.tex`, Corollary `t7:p02:MGF` (formula
`t7:p02:MGF-equation`), which follows from Lemma `t7:p02:GP` (the geometric Brascamp–Lieb
inequality for the Gaussian measure, continuous family). Here `I_x(z) = 1{(x, √v·|r(x)|·z) ∈ S}`,
and at the inputs with `r(x) = 0` the indicator does not depend on `M`. -/
def GaussFrameMGF : Prop :=
  ∀ (N q m : ℕ) (μ : Measure (Fin N → ℝ)), IsProbabilityMeasure μ →
    ∀ (b : Fin m → ℝ) (h : (Fin N → ℝ) → Fin m → ℝ), Measurable h →
    ∀ S : Set ((Fin N → ℝ) × (Fin q → ℝ)), MeasurableSet S →
    ∀ v L : ℝ, 0 < v → 0 < L →
    (∀ w : Fin m → ℝ, ∫ x, (∑ j, eDir b (h x) j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) →
    ∀ s : ℝ,
      ∫ M, exp (s * μ.real {x | (x, M.mulVec (res b (h x))) ∈ S} / L) ∂gaussMat q m v ≤
        (1 - (∫ M, μ.real {x | (x, M.mulVec (res b (h x))) ∈ S} ∂gaussMat q m v) +
          (∫ M, μ.real {x | (x, M.mulVec (res b (h x))) ∈ S} ∂gaussMat q m v) * exp s) ^ (1 / L)

variable {n : ℕ}

/-- **(FRAME-W), the frame bound of the World network.** For every retained value `c` in `E`:
the unit directions `e_W(u)` of the residual `r_W(u) = a₂^W(u) − λ_W(u) b_W` of the last hidden
vector of `W`, `u` uniform on the unit sphere of `ℝ^{2n}`, have the frame bound `L_W`:
`∫ ⟨e_W(u), w⟩² du ≤ L_W·|w|²` for every `w`. A statement about `(W₁, W₂)` only.

Paper statement that proves it: `theorem7-02-world.tex`, Input `t7:p02:input-frame`
(formula `t7:p02:frame-conclusion`, `L_W(n) = c_W(n)/n` on the hidden event `H_W`). It is a
SUPPLIED INPUT of the paper (its source chain is in Part 02 of the paper). -/
def FRAME_W_hyp (D : Centres n) (LW : ℝ) (E : Set (Ret n)) : Prop :=
  ∀ c ∈ E, ∀ w : Fin (mW n) → ℝ,
    ∫ u, (∑ j, eDir (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
      LW * ∑ j, w j ^ 2

/-- The last hidden vector of `A` at the stand-in input `sphPt (ĉ + τ₀ ξ)`. -/
noncomputable def hStand (D : Design n) (c : Ret n) (ξ : Fin n → ℝ) : Fin (mA n) → ℝ :=
  hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ))

/-- **(FRAME-A), the frame bound of the Agent network under the stand-in input distribution.**
For every retained value `c` in `E`: the unit directions `e(x)` of the residual
`r(x) = a₂(x) − λ(x) b` of the last hidden vector of `A`, `x = sphPt (ĉ + τ₀ ξ)`, `ξ` standard
Gaussian, have the frame bound `L_A`. A statement about the retained data only.

Paper statement that proves it: `theorem7-09-assembly.tex`, Lemma `t7:p09:frame-junction`,
formula `t7:p09:frame` (`n L_A ≤ c_frame`), from Lemma `t7:p04:split`, Proposition
`t7:p04:certificate`, Proposition `t7:p05:certificate` and Proposition `t7:p06:cutoffs`. -/
def FRAME_A_hyp (D : Design n) (LA : ℝ) (E : Set (Ret n)) : Prop :=
  ∀ c ∈ E, ∀ w : Fin (mA n) → ℝ,
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      LA * ∑ j, w j ^ 2

/-! ## The two probabilities in the frame form -/

lemma mlpEval_netOf {k m q : ℕ} (b : HidParam k m → Fin m → ℝ) (θ : HidParam k m)
    (c : Fin q → ℝ) (M' : Matrix (Fin q) (Fin m) ℝ) (z : Fin k → ℝ) :
    mlpEval (netOf b θ c M') z =
      lam (b θ) (hid2 θ.1 θ.2 z) • c + M'.mulVec (res (b θ) (hid2 θ.1 θ.2 z)) :=
  mlp2_reb θ.1 θ.2 (b θ) c M' z

/-- The set `S` of the World stage: the pairs (input `u`, residual output `y`) at which the
classifier is true on `A(sphPt (λ_W(u)·ĉ + y))`. -/
def setW (D : Centres n) (t : ℝ) (c : Ret n) (A : MlpParam n (mA n) n) :
    Set ((Fin (2 * n) → ℝ) × (Fin n → ℝ)) :=
  {y | classifier c.2.2 t (mlpEval A
    (sphPt (lam (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 y.1) • c.1.2 + y.2)))}

/-- **The target in the frame form**: `p = Pr_u((u, ω_W r_W(u)) ∈ S)`. -/
theorem pRes_eq_frame (D : Centres n) (t : ℝ) (c : Ret n) (ω : ResW n × ResA n) :
    pRes D t c ω = (uniformSphere (2 * n)).real
      {u | (u, ω.1.mulVec (res (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u))) ∈
        setW D t c (agentOf D c ω.2)} := by
  have e : hitSet (rebuild D c ω).1 (rebuild D c ω).2.1 (rebuild D c ω).2.2 t =
      {u | (u, ω.1.mulVec (res (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u))) ∈
        setW D t c (agentOf D c ω.2)} := by
    ext u
    have h1 : mlpEval (rebuild D c ω).1 u =
        lam (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u) • c.1.2 +
          ω.1.mulVec (res (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u)) :=
      mlpEval_netOf D.bW c.1.1 c.1.2 ω.1 u
    change classifier c.2.2 t (mlpEval (agentOf D c ω.2) (sphPt (mlpEval (rebuild D c ω).1 u))) ↔
      classifier c.2.2 t (mlpEval (agentOf D c ω.2)
        (sphPt (lam (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u) • c.1.2 +
          ω.1.mulVec (res (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u)))))
    rw [h1]
  unfold pRes pTargetT pTarget
  rw [e]

lemma measurableSet_setW (D : Centres n) (t : ℝ) (c : Ret n) (A : MlpParam n (mA n) n) :
    MeasurableSet (setW D t c A) := by
  have h1 : Measurable (fun y : (Fin (2 * n) → ℝ) × (Fin n → ℝ) =>
      lam (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 y.1) • c.1.2 + y.2) :=
    ((((measurable_lam (D.bW c.1.1)).comp
      ((continuous_hid2 c.1.1.1 c.1.1.2).measurable.comp measurable_fst)).smul_const c.1.2).add
      measurable_snd)
  have h2 : Measurable (fun y : (Fin (2 * n) → ℝ) × (Fin n → ℝ) =>
      mlpEval c.2.2 (mlpEval A
        (sphPt (lam (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 y.1) • c.1.2 + y.2))) 0) :=
    (measurable_pi_apply 0).comp ((continuous_mlpEval c.2.2).measurable.comp
      ((continuous_mlpEval A).measurable.comp (measurable_sphPt.comp h1)))
  exact measurableSet_lt measurable_const h2

/-- The set `S` of the Agent stage: the pairs (noise `ξ` of the stand-in input, residual output
`y`) at which the classifier is true on `λ(x)·c_A + y`. -/
def setA (D : Design n) (t : ℝ) (c : Ret n) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {y | classifier c.2.2 t (lam (D.bA c.1 c.2.1.1) (hStand D c y.1) • c.2.1.2 + y.2)}

/-- **The stand-in probability in the frame form**: `P = Pr_ξ((ξ, ω_A r(x_ξ)) ∈ S)`. -/
theorem PStand_eq_frame (D : Design n) (t : ℝ) (c : Ret n) (ωA : ResA n) :
    PStand D t c ωA = (stdGauss (Fin n)).real
      {ξ | (ξ, ωA.mulVec (res (D.bA c.1 c.2.1.1) (hStand D c ξ))) ∈ setA D t c} := by
  have e : {ξ : Fin n → ℝ | classifier c.2.2 t
      (mlpEval (agentOf D.toCentres c ωA) (sphPt (c.1.2 + D.tau0 c • ξ)))} =
      {ξ | (ξ, ωA.mulVec (res (D.bA c.1 c.2.1.1) (hStand D c ξ))) ∈ setA D t c} := by
    ext ξ
    have h1 : mlpEval (agentOf D.toCentres c ωA) (sphPt (c.1.2 + D.tau0 c • ξ)) =
        lam (D.bA c.1 c.2.1.1) (hStand D c ξ) • c.2.1.2 +
          ωA.mulVec (res (D.bA c.1 c.2.1.1) (hStand D c ξ)) :=
      mlpEval_netOf (D.bA c.1) c.2.1.1 c.2.1.2 ωA _
    change classifier c.2.2 t (mlpEval (agentOf D.toCentres c ωA) (sphPt (c.1.2 + D.tau0 c • ξ))) ↔
      classifier c.2.2 t (lam (D.bA c.1 c.2.1.1) (hStand D c ξ) • c.2.1.2 +
        ωA.mulVec (res (D.bA c.1 c.2.1.1) (hStand D c ξ)))
    rw [h1]
  unfold PStand
  rw [e]

lemma measurable_hStand (D : Design n) (c : Ret n) : Measurable (hStand D c) :=
  (continuous_hid2 c.2.1.1.1 c.2.1.1.2).measurable.comp
    (measurable_sphPt.comp (measurable_const.add (measurable_const_smul (D.tau0 c))))

lemma measurableSet_setA (D : Design n) (t : ℝ) (c : Ret n) : MeasurableSet (setA D t c) := by
  have h1 : Measurable (fun y : (Fin n → ℝ) × (Fin n → ℝ) =>
      lam (D.bA c.1 c.2.1.1) (hStand D c y.1) • c.2.1.2 + y.2) :=
    ((((measurable_lam (D.bA c.1 c.2.1.1)).comp
      ((measurable_hStand D c).comp measurable_fst)).smul_const c.2.1.2).add measurable_snd)
  have h2 : Measurable (fun y : (Fin n → ℝ) × (Fin n → ℝ) =>
      mlpEval c.2.2 (lam (D.bA c.1 c.2.1.1) (hStand D c y.1) • c.2.1.2 + y.2) 0) :=
    (measurable_pi_apply 0).comp ((continuous_mlpEval c.2.2).measurable.comp h1)
  exact measurableSet_lt measurable_const h2

/-! ## (GP-W) and (GP-A) from the Gaussian inequality and the frame bounds -/

lemma mW_pos (hn : 1 ≤ n) : 0 < mW n := by
  unfold mW
  exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)

lemma mA_pos (hn : 1 ≤ n) : 0 < mA n := by
  unfold mA
  positivity

lemma integral_mem_01 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (h0 : ∀ ω, 0 ≤ f ω) (h1 : ∀ ω, f ω ≤ 1) :
    0 ≤ ∫ ω, f ω ∂μ ∧ ∫ ω, f ω ∂μ ≤ 1 := by
  refine ⟨integral_nonneg h0, ?_⟩
  have hi : Integrable f μ := by
    refine Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 ω)]
    exact h1 ω
  have := integral_mono hi (integrable_const (1 : ℝ)) h1
  simpa using this

/-- **(GP-W) from the Gaussian frame inequality and the World frame bound.** -/
theorem gpw_of_frame (hn : 1 ≤ n) (hG : GaussFrameMGF) (D : Centres n) (t : ℝ) {LW : ℝ}
    (hLW : 0 < LW) {E : Set (Ret n)} (hF : FRAME_W_hyp D LW E) : GPW_hyp D t LW E := by
  intro c hc ωA s
  have hprob := BstLean.Part29.uniformSphere_isProbability (2 * n) (by omega)
  have hv : (0 : ℝ) < 2 / (mW n : ℝ) := by
    have : (0 : ℝ) < (mW n : ℝ) := by exact_mod_cast mW_pos hn
    positivity
  have e : ∀ ωW : ResW n, (uniformSphere (2 * n)).real
        {u | (u, ωW.mulVec (res (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u))) ∈
          setW D t c (agentOf D c ωA)} = pRes D t c (ωW, ωA) :=
    fun ωW => (pRes_eq_frame D t c (ωW, ωA)).symm
  have key := hG (2 * n) n (mW n) (uniformSphere (2 * n)) hprob (D.bW c.1.1)
    (hid2 c.1.1.1 c.1.1.2) (continuous_hid2 c.1.1.1 c.1.1.2).measurable
    (setW D t c (agentOf D c ωA)) (measurableSet_setW D t c _) (2 / (mW n : ℝ)) LW hv hLW
    (hF c hc)
  have hm : Measurable (fun ωW : ResW n => pRes D t c (ωW, ωA)) := by
    have h := (measurable_pRes D t).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const) :
        Measurable (fun ωW : ResW n => ((c, (ωW, ωA)) : Ret n × (ResW n × ResA n))))
    exact h
  obtain ⟨hq0, hq1⟩ := integral_mem_01 (resW n) hm (fun ωW => pRes_nonneg D t c _)
    (fun ωW => pRes_le_one hn D t c _)
  refine gp_of_primitive (resW n) (p := fun ωW : ResW n => pRes D t c (ωW, ωA)) hLW hq0 hq1
    (fun s' => ?_) s
  have k' := key s'
  simp only [e] at k'
  exact k'

/-- **(GP-A) from the Gaussian frame inequality and the Agent frame bound.** -/
theorem gpa_of_frame (hn : 1 ≤ n) (hG : GaussFrameMGF) (D : Design n) (t : ℝ) {LA : ℝ}
    (hLA : 0 < LA) {E : Set (Ret n)} (hF : FRAME_A_hyp D LA E) : GPA_hyp D t LA E := by
  intro c hc u
  have hv : (0 : ℝ) < 2 / (mA n : ℝ) := by
    have : (0 : ℝ) < (mA n : ℝ) := by exact_mod_cast mA_pos hn
    positivity
  have e : ∀ ωA : ResA n, (stdGauss (Fin n)).real
        {ξ | (ξ, ωA.mulVec (res (D.bA c.1 c.2.1.1) (hStand D c ξ))) ∈ setA D t c} =
      PStand D t c ωA := fun ωA => (PStand_eq_frame D t c ωA).symm
  have key := hG n n (mA n) (stdGauss (Fin n)) inferInstance (D.bA c.1 c.2.1.1)
    (hStand D c) (measurable_hStand D c) (setA D t c) (measurableSet_setA D t c)
    (2 / (mA n : ℝ)) LA hv hLA (hF c hc)
  obtain ⟨hq0, hq1⟩ := integral_mem_01 (resA n) (measurable_PStand D t c)
    (fun ωA => PStand_nonneg D t c _) (fun ωA => PStand_le_one D t c _)
  refine gp_of_primitive (resA n) (p := fun ωA : ResA n => PStand D t c ωA) hLA hq0 hq1
    (fun s' => ?_) u
  have k' := key s'
  simp only [e] at k'
  exact k'

end BstLean.Part157

open BstLean.Part157 in
#print axioms gpw_of_frame
open BstLean.Part157 in
#print axioms gpa_of_frame
